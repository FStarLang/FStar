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
  fun uu____2017  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2115 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2115 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2115 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2115 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2181 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2181  in
                  let uu____2184 =
                    let uu____2191 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2191
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2184 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2212 ->
                            let uu____2219 =
                              let uu____2224 =
                                FStar_List.map
                                  (fun uu____2237  ->
                                     match uu____2237 with
                                     | (x,i) ->
                                         let uu____2248 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2248, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2224  in
                            uu____2219 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let prob =
                        let uu____2254 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2254;
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
                  (let uu____2318 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2318 with
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
                  (let uu____2397 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2397 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2433 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2433 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2433 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2433 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2484 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2521 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2521]  in
                        let uu____2534 =
                          let uu____2537 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2537  in
                        let uu____2540 =
                          let uu____2543 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2543  in
                        (bs, uu____2534, uu____2540)
                     in
                  match uu____2484 with
                  | (bs,lg_ty,elt) ->
                      let uu____2565 =
                        let uu____2572 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___161_2580 = wl  in
                           {
                             attempting = (uu___161_2580.attempting);
                             wl_deferred = (uu___161_2580.wl_deferred);
                             ctr = (uu___161_2580.ctr);
                             defer_ok = (uu___161_2580.defer_ok);
                             smt_ok = (uu___161_2580.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___161_2580.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2572
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2565 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2592 =
                                   let uu____2597 =
                                     let uu____2598 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2598]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2597
                                    in
                                 uu____2592 FStar_Pervasives_Native.None loc
                              in
                           let prob =
                             let uu____2622 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2622;
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
                let uu____2664 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2664;
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
  'Auu____2676 .
    worklist ->
      'Auu____2676 FStar_TypeChecker_Common.problem ->
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
        let uu____2726 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2726
        then
          let uu____2727 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2728 = prob_to_string env d  in
          let uu____2729 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2727 uu____2728 uu____2729 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2735 -> failwith "impossible"  in
           let uu____2736 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2748 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2749 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2748, uu____2749)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2753 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2754 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2753, uu____2754)
              in
           match uu____2736 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___130_2772  ->
            match uu___130_2772 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2784 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2788 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  def_check_closed_in t.FStar_Syntax_Syntax.pos "commit"
                    uu____2788 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___131_2813  ->
           match uu___131_2813 with
           | UNIV uu____2816 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2823 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2823
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
        (fun uu___132_2847  ->
           match uu___132_2847 with
           | UNIV (u',t) ->
               let uu____2852 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2852
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2856 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2867 =
        let uu____2868 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2868
         in
      FStar_Syntax_Subst.compress uu____2867
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2879 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2879
  
let norm_arg :
  'Auu____2886 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2886) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2886)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2909 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2909, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2950  ->
              match uu____2950 with
              | (x,imp) ->
                  let uu____2961 =
                    let uu___162_2962 = x  in
                    let uu____2963 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___162_2962.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___162_2962.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2963
                    }  in
                  (uu____2961, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2984 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2984
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2988 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2988
        | uu____2991 -> u2  in
      let uu____2992 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2992
  
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
                (let uu____3114 = norm_refinement env t12  in
                 match uu____3114 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3131;
                     FStar_Syntax_Syntax.vars = uu____3132;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3158 =
                       let uu____3159 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3160 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3159 uu____3160
                        in
                     failwith uu____3158)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3176 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3176
          | FStar_Syntax_Syntax.Tm_uinst uu____3177 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3216 =
                   let uu____3217 = FStar_Syntax_Subst.compress t1'  in
                   uu____3217.FStar_Syntax_Syntax.n  in
                 match uu____3216 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3234 -> aux true t1'
                 | uu____3241 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3258 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3291 =
                   let uu____3292 = FStar_Syntax_Subst.compress t1'  in
                   uu____3292.FStar_Syntax_Syntax.n  in
                 match uu____3291 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3309 -> aux true t1'
                 | uu____3316 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3333 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3380 =
                   let uu____3381 = FStar_Syntax_Subst.compress t1'  in
                   uu____3381.FStar_Syntax_Syntax.n  in
                 match uu____3380 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3398 -> aux true t1'
                 | uu____3405 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3422 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3439 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3456 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3473 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3490 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3519 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3552 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3575 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3606 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3635 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3674 ->
              let uu____3681 =
                let uu____3682 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3683 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3682 uu____3683
                 in
              failwith uu____3681
          | FStar_Syntax_Syntax.Tm_ascribed uu____3698 ->
              let uu____3725 =
                let uu____3726 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3727 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3726 uu____3727
                 in
              failwith uu____3725
          | FStar_Syntax_Syntax.Tm_delayed uu____3742 ->
              let uu____3767 =
                let uu____3768 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3769 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3768 uu____3769
                 in
              failwith uu____3767
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3784 =
                let uu____3785 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3786 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3785 uu____3786
                 in
              failwith uu____3784
           in
        let uu____3801 = whnf env t1  in aux false uu____3801
  
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
      let uu____3847 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3847 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3883 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3883, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3894 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3894 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3921 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3921 with
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
                          (fun uu___134_4468  ->
                             match uu___134_4468 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4472 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4472]
                             | uu____4473 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4458 FStar_List.rev  in
                    let uu____4490 =
                      let uu____4497 =
                        let uu____4504 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___135_4522  ->
                                  match uu___135_4522 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4526 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4526]
                                  | uu____4527 -> []))
                           in
                        FStar_All.pipe_right uu____4504 FStar_List.rev  in
                      let uu____4544 =
                        let uu____4547 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4547  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4497 uu____4544
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4490 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4576  ->
                                match uu____4576 with
                                | (x,i) ->
                                    let uu____4587 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4587, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4610  ->
                                match uu____4610 with
                                | (a,i) ->
                                    let uu____4621 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4621, i)) args_sol
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
           | uu____4637 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4657 =
          let uu____4678 =
            let uu____4679 = FStar_Syntax_Subst.compress k  in
            uu____4679.FStar_Syntax_Syntax.n  in
          match uu____4678 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4748 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4748)
              else
                (let uu____4778 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4778 with
                 | (ys',t1,uu____4809) ->
                     let uu____4814 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4814))
          | uu____4847 ->
              let uu____4848 =
                let uu____4853 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4853)  in
              ((ys, t), uu____4848)
           in
        match uu____4657 with
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
                 let uu____4930 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4930 c  in
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
               (let uu____5004 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5004
                then
                  let uu____5005 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5006 = print_ctx_uvar uv  in
                  let uu____5007 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5005 uu____5006 uu____5007
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5013 =
                   let uu____5014 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____5014  in
                 let uu____5015 =
                   let uu____5018 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5018
                    in
                 def_check_closed_in (p_loc prob) uu____5013 uu____5015 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uu____5037 = p_guard_uvar prob  in
             match uu____5037 with
             | (xs,uv) ->
                 let fail1 uu____5049 =
                   let uu____5050 =
                     let uu____5051 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____5052 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____5051 uu____5052
                      in
                   failwith uu____5050  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____5102  ->
                           match uu____5102 with
                           | (a,i) ->
                               let uu____5115 =
                                 let uu____5116 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____5116.FStar_Syntax_Syntax.n  in
                               (match uu____5115 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____5134 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____5142 =
                     let uu____5143 = is_flex g  in
                     Prims.op_Negation uu____5143  in
                   if uu____5142
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5147 = destruct_flex_t g wl  in
                      match uu____5147 with
                      | ((uu____5152,uv1,args),wl1) ->
                          ((let uu____5157 = args_as_binders args  in
                            assign_solution uu____5157 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___163_5159 = wl1  in
                   {
                     attempting = (uu___163_5159.attempting);
                     wl_deferred = (uu___163_5159.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___163_5159.defer_ok);
                     smt_ok = (uu___163_5159.smt_ok);
                     tcenv = (uu___163_5159.tcenv);
                     wl_implicits = (uu___163_5159.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5180 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5180
         then
           let uu____5181 = FStar_Util.string_of_int pid  in
           let uu____5182 =
             let uu____5183 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5183 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5181 uu____5182
         else ());
        commit sol;
        (let uu___164_5190 = wl  in
         {
           attempting = (uu___164_5190.attempting);
           wl_deferred = (uu___164_5190.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___164_5190.defer_ok);
           smt_ok = (uu___164_5190.smt_ok);
           tcenv = (uu___164_5190.tcenv);
           wl_implicits = (uu___164_5190.wl_implicits)
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
             | (uu____5252,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5280 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5280
              in
           (let uu____5286 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5286
            then
              let uu____5287 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5288 =
                let uu____5289 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5289 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5287 uu____5288
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
        let uu____5314 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5314 FStar_Util.set_elements  in
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
      let uu____5348 = occurs uk t  in
      match uu____5348 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5377 =
                 let uu____5378 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5379 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5378 uu____5379
                  in
               FStar_Pervasives_Native.Some uu____5377)
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
            let uu____5468 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5468 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5512 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5560  ->
             match uu____5560 with
             | (x,uu____5570) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5583 = FStar_List.last bs  in
      match uu____5583 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5601) ->
          let uu____5606 =
            FStar_Util.prefix_until
              (fun uu___136_5621  ->
                 match uu___136_5621 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5623 -> false) g
             in
          (match uu____5606 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5636,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5672 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5672 with
        | (pfx,uu____5682) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5694 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5694 with
             | (uu____5701,src',wl1) ->
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
                 | uu____5801 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5802 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5856  ->
                  fun uu____5857  ->
                    match (uu____5856, uu____5857) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5938 =
                          let uu____5939 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5939
                           in
                        if uu____5938
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5964 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5964
                           then
                             let uu____5977 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5977)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5802 with | (isect,uu____6014) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6043 'Auu____6044 .
    (FStar_Syntax_Syntax.bv,'Auu____6043) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____6044) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6101  ->
              fun uu____6102  ->
                match (uu____6101, uu____6102) with
                | ((a,uu____6120),(b,uu____6122)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6137 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6137) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6167  ->
           match uu____6167 with
           | (y,uu____6173) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6182 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6182) FStar_Pervasives_Native.tuple2
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
                   let uu____6312 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6312
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6332 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6375 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6413 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6426 -> false
  
let string_of_option :
  'Auu____6433 .
    ('Auu____6433 -> Prims.string) ->
      'Auu____6433 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___137_6448  ->
      match uu___137_6448 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6454 = f x  in Prims.strcat "Some " uu____6454
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___138_6459  ->
    match uu___138_6459 with
    | MisMatch (d1,d2) ->
        let uu____6470 =
          let uu____6471 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6472 =
            let uu____6473 =
              let uu____6474 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6474 ")"  in
            Prims.strcat ") (" uu____6473  in
          Prims.strcat uu____6471 uu____6472  in
        Prims.strcat "MisMatch (" uu____6470
    | HeadMatch u ->
        let uu____6476 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6476
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___139_6481  ->
    match uu___139_6481 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6496 -> HeadMatch false
  
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
          let uu____6510 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6510 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6521 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6544 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6553 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6581 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6581
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6582 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6583 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6584 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6599 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6612 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6636) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6642,uu____6643) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6685) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6706;
             FStar_Syntax_Syntax.index = uu____6707;
             FStar_Syntax_Syntax.sort = t2;_},uu____6709)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6716 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6717 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6718 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6731 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6738 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6756 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6756
  
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
            let uu____6783 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6783
            then FullMatch
            else
              (let uu____6785 =
                 let uu____6794 =
                   let uu____6797 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6797  in
                 let uu____6798 =
                   let uu____6801 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6801  in
                 (uu____6794, uu____6798)  in
               MisMatch uu____6785)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6807),FStar_Syntax_Syntax.Tm_uinst (g,uu____6809)) ->
            let uu____6818 = head_matches env f g  in
            FStar_All.pipe_right uu____6818 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6821 = FStar_Const.eq_const c d  in
            if uu____6821
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6828),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6830)) ->
            let uu____6871 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6871
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6878),FStar_Syntax_Syntax.Tm_refine (y,uu____6880)) ->
            let uu____6889 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6889 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6891),uu____6892) ->
            let uu____6897 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6897 head_match
        | (uu____6898,FStar_Syntax_Syntax.Tm_refine (x,uu____6900)) ->
            let uu____6905 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6905 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6906,FStar_Syntax_Syntax.Tm_type
           uu____6907) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6908,FStar_Syntax_Syntax.Tm_arrow uu____6909) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6935),FStar_Syntax_Syntax.Tm_app (head',uu____6937))
            ->
            let uu____6978 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6978 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6980),uu____6981) ->
            let uu____7002 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7002 head_match
        | (uu____7003,FStar_Syntax_Syntax.Tm_app (head1,uu____7005)) ->
            let uu____7026 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7026 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7027,FStar_Syntax_Syntax.Tm_let
           uu____7028) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7053,FStar_Syntax_Syntax.Tm_match uu____7054) ->
            HeadMatch true
        | uu____7099 ->
            let uu____7104 =
              let uu____7113 = delta_depth_of_term env t11  in
              let uu____7116 = delta_depth_of_term env t21  in
              (uu____7113, uu____7116)  in
            MisMatch uu____7104
  
let head_matches_delta :
  'Auu____7133 .
    FStar_TypeChecker_Env.env ->
      'Auu____7133 ->
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
            (let uu____7182 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7182
             then
               let uu____7183 = FStar_Syntax_Print.term_to_string t  in
               let uu____7184 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7183 uu____7184
             else ());
            (let uu____7186 =
               let uu____7187 = FStar_Syntax_Util.un_uinst head1  in
               uu____7187.FStar_Syntax_Syntax.n  in
             match uu____7186 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7193 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7193 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7207 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7207
                        then
                          let uu____7208 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7208
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7210 ->
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
                      ((let uu____7221 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7221
                        then
                          let uu____7222 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7223 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7222
                            uu____7223
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7225 -> FStar_Pervasives_Native.None)
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
            (let uu____7363 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7363
             then
               let uu____7364 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7365 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7366 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7364
                 uu____7365 uu____7366
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7390 =
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
               match uu____7390 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7435 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7435 with
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
                  uu____7467),uu____7468)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7486 =
                      let uu____7495 = maybe_inline t11  in
                      let uu____7498 = maybe_inline t21  in
                      (uu____7495, uu____7498)  in
                    match uu____7486 with
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
                 (uu____7535,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7536))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7554 =
                      let uu____7563 = maybe_inline t11  in
                      let uu____7566 = maybe_inline t21  in
                      (uu____7563, uu____7566)  in
                    match uu____7554 with
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
             | MisMatch uu____7615 -> fail1 n_delta r t11 t21
             | uu____7624 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7637 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7637
           then
             let uu____7638 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7639 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7640 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7647 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7665 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7665
                    (fun uu____7699  ->
                       match uu____7699 with
                       | (t11,t21) ->
                           let uu____7706 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7707 =
                             let uu____7708 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7708  in
                           Prims.strcat uu____7706 uu____7707))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7638 uu____7639 uu____7640 uu____7647
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7720 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7720 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___140_7733  ->
    match uu___140_7733 with
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
      let uu___165_7770 = p  in
      let uu____7773 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7774 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___165_7770.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7773;
        FStar_TypeChecker_Common.relation =
          (uu___165_7770.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7774;
        FStar_TypeChecker_Common.element =
          (uu___165_7770.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___165_7770.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___165_7770.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___165_7770.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___165_7770.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___165_7770.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7788 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7788
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7793 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7815 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7815 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7823 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7823 with
           | (lh,lhs_args) ->
               let uu____7864 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7864 with
                | (rh,rhs_args) ->
                    let uu____7905 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7918,FStar_Syntax_Syntax.Tm_uvar uu____7919)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8000 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8023,uu____8024)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8041,FStar_Syntax_Syntax.Tm_uvar uu____8042)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8059,FStar_Syntax_Syntax.Tm_arrow uu____8060)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8090 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8090.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8090.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8090.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8090.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8090.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8090.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8090.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8090.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8090.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8093,FStar_Syntax_Syntax.Tm_type uu____8094)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8112 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8112.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8112.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8112.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8112.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8112.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8112.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8112.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8112.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8112.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8115,FStar_Syntax_Syntax.Tm_uvar uu____8116)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8134 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8134.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8134.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8134.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8134.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8134.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8134.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8134.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8134.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8134.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8137,FStar_Syntax_Syntax.Tm_uvar uu____8138)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8155,uu____8156)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8173,FStar_Syntax_Syntax.Tm_uvar uu____8174)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8191,uu____8192) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7905 with
                     | (rank,tp1) ->
                         let uu____8205 =
                           FStar_All.pipe_right
                             (let uu___167_8209 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___167_8209.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___167_8209.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___167_8209.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___167_8209.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___167_8209.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___167_8209.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___167_8209.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___167_8209.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___167_8209.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8205))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8215 =
            FStar_All.pipe_right
              (let uu___168_8219 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___168_8219.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___168_8219.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___168_8219.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___168_8219.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___168_8219.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___168_8219.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___168_8219.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___168_8219.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___168_8219.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8215)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8280 probs =
      match uu____8280 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8361 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8382 = rank wl.tcenv hd1  in
               (match uu____8382 with
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
                      (let uu____8441 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8445 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8445)
                          in
                       if uu____8441
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
          let uu____8513 = FStar_Syntax_Util.head_and_args t  in
          match uu____8513 with
          | (hd1,uu____8529) ->
              let uu____8550 =
                let uu____8551 = FStar_Syntax_Subst.compress hd1  in
                uu____8551.FStar_Syntax_Syntax.n  in
              (match uu____8550 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8555) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8589  ->
                           match uu____8589 with
                           | (y,uu____8595) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8609  ->
                                       match uu____8609 with
                                       | (x,uu____8615) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8616 -> false)
           in
        let uu____8617 = rank tcenv p  in
        match uu____8617 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8624 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8651 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8665 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8679 -> false
  
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
                        let uu____8731 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8731 with
                        | (k,uu____8737) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8747 -> false)))
            | uu____8748 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8800 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8806 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8806 = (Prims.parse_int "0")))
                           in
                        if uu____8800 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8822 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8828 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8828 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8822)
               in
            let uu____8829 = filter1 u12  in
            let uu____8832 = filter1 u22  in (uu____8829, uu____8832)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8861 = filter_out_common_univs us1 us2  in
                (match uu____8861 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8920 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8920 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8923 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8933 =
                          let uu____8934 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8935 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8934
                            uu____8935
                           in
                        UFailed uu____8933))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8959 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8959 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8985 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8985 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8988 ->
                let uu____8993 =
                  let uu____8994 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8995 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8994
                    uu____8995 msg
                   in
                UFailed uu____8993
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8996,uu____8997) ->
              let uu____8998 =
                let uu____8999 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9000 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8999 uu____9000
                 in
              failwith uu____8998
          | (FStar_Syntax_Syntax.U_unknown ,uu____9001) ->
              let uu____9002 =
                let uu____9003 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9004 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9003 uu____9004
                 in
              failwith uu____9002
          | (uu____9005,FStar_Syntax_Syntax.U_bvar uu____9006) ->
              let uu____9007 =
                let uu____9008 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9009 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9008 uu____9009
                 in
              failwith uu____9007
          | (uu____9010,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9011 =
                let uu____9012 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9013 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9012 uu____9013
                 in
              failwith uu____9011
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9037 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9037
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9051 = occurs_univ v1 u3  in
              if uu____9051
              then
                let uu____9052 =
                  let uu____9053 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9054 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9053 uu____9054
                   in
                try_umax_components u11 u21 uu____9052
              else
                (let uu____9056 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9056)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9068 = occurs_univ v1 u3  in
              if uu____9068
              then
                let uu____9069 =
                  let uu____9070 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9071 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9070 uu____9071
                   in
                try_umax_components u11 u21 uu____9069
              else
                (let uu____9073 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9073)
          | (FStar_Syntax_Syntax.U_max uu____9074,uu____9075) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9081 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9081
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9083,FStar_Syntax_Syntax.U_max uu____9084) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9090 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9090
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9092,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9093,FStar_Syntax_Syntax.U_name
             uu____9094) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9095) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9096) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9097,FStar_Syntax_Syntax.U_succ
             uu____9098) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9099,FStar_Syntax_Syntax.U_zero
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
      let uu____9199 = bc1  in
      match uu____9199 with
      | (bs1,mk_cod1) ->
          let uu____9243 = bc2  in
          (match uu____9243 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9354 = aux xs ys  in
                     (match uu____9354 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9437 =
                       let uu____9444 = mk_cod1 xs  in ([], uu____9444)  in
                     let uu____9447 =
                       let uu____9454 = mk_cod2 ys  in ([], uu____9454)  in
                     (uu____9437, uu____9447)
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
                  let uu____9524 =
                    let uu____9525 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9525 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9524
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9530 = has_type_guard t1 t2  in (uu____9530, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9531 = has_type_guard t2 t1  in (uu____9531, wl)
  
let is_flex_pat :
  'Auu____9540 'Auu____9541 'Auu____9542 .
    ('Auu____9540,'Auu____9541,'Auu____9542 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___141_9555  ->
    match uu___141_9555 with
    | (uu____9564,uu____9565,[]) -> true
    | uu____9568 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9599 = f  in
      match uu____9599 with
      | (uu____9606,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9607;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9608;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9611;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9612;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9613;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9665  ->
                 match uu____9665 with
                 | (y,uu____9671) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9793 =
                  let uu____9806 =
                    let uu____9809 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9809  in
                  ((FStar_List.rev pat_binders), uu____9806)  in
                FStar_Pervasives_Native.Some uu____9793
            | (uu____9836,[]) ->
                let uu____9859 =
                  let uu____9872 =
                    let uu____9875 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9875  in
                  ((FStar_List.rev pat_binders), uu____9872)  in
                FStar_Pervasives_Native.Some uu____9859
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9940 =
                  let uu____9941 = FStar_Syntax_Subst.compress a  in
                  uu____9941.FStar_Syntax_Syntax.n  in
                (match uu____9940 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9959 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9959
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___169_9980 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___169_9980.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___169_9980.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9984 =
                            let uu____9985 =
                              let uu____9992 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9992)  in
                            FStar_Syntax_Syntax.NT uu____9985  in
                          [uu____9984]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___170_10004 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_10004.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___170_10004.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10005 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10033 =
                  let uu____10046 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10046  in
                (match uu____10033 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10109 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10136 ->
               let uu____10137 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10137 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10413 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10413
       then
         let uu____10414 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10414
       else ());
      (let uu____10416 = next_prob probs  in
       match uu____10416 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___171_10443 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___171_10443.wl_deferred);
               ctr = (uu___171_10443.ctr);
               defer_ok = (uu___171_10443.defer_ok);
               smt_ok = (uu___171_10443.smt_ok);
               tcenv = (uu___171_10443.tcenv);
               wl_implicits = (uu___171_10443.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10451 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10451
                 then
                   let uu____10452 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10452
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
                           (let uu___172_10457 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___172_10457.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___172_10457.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___172_10457.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___172_10457.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___172_10457.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___172_10457.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___172_10457.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___172_10457.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___172_10457.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10479 ->
                let uu____10488 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10547  ->
                          match uu____10547 with
                          | (c,uu____10555,uu____10556) -> c < probs.ctr))
                   in
                (match uu____10488 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10597 =
                            let uu____10602 =
                              FStar_List.map
                                (fun uu____10617  ->
                                   match uu____10617 with
                                   | (uu____10628,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10602, (probs.wl_implicits))  in
                          Success uu____10597
                      | uu____10631 ->
                          let uu____10640 =
                            let uu___173_10641 = probs  in
                            let uu____10642 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10661  ->
                                      match uu____10661 with
                                      | (uu____10668,uu____10669,y) -> y))
                               in
                            {
                              attempting = uu____10642;
                              wl_deferred = rest;
                              ctr = (uu___173_10641.ctr);
                              defer_ok = (uu___173_10641.defer_ok);
                              smt_ok = (uu___173_10641.smt_ok);
                              tcenv = (uu___173_10641.tcenv);
                              wl_implicits = (uu___173_10641.wl_implicits)
                            }  in
                          solve env uu____10640))))

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
            let uu____10676 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10676 with
            | USolved wl1 ->
                let uu____10678 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10678
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
                  let uu____10730 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10730 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10733 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10745;
                  FStar_Syntax_Syntax.vars = uu____10746;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10749;
                  FStar_Syntax_Syntax.vars = uu____10750;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10762,uu____10763) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10770,FStar_Syntax_Syntax.Tm_uinst uu____10771) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10778 -> USolved wl

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
            ((let uu____10788 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10788
              then
                let uu____10789 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10789 msg
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
               let uu____10875 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10875 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10928 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10928
                then
                  let uu____10929 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10930 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10929 uu____10930
                else ());
               (let uu____10932 = head_matches_delta env1 () t1 t2  in
                match uu____10932 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10977 = eq_prob t1 t2 wl2  in
                         (match uu____10977 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10998 ->
                         let uu____11007 = eq_prob t1 t2 wl2  in
                         (match uu____11007 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11056 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11071 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11072 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11071, uu____11072)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11077 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11078 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11077, uu____11078)
                            in
                         (match uu____11056 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11109 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11109 with
                                | (t1_hd,t1_args) ->
                                    let uu____11148 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11148 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11202 =
                                              let uu____11209 =
                                                let uu____11218 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11218 :: t1_args  in
                                              let uu____11231 =
                                                let uu____11238 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11238 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11279  ->
                                                   fun uu____11280  ->
                                                     fun uu____11281  ->
                                                       match (uu____11279,
                                                               uu____11280,
                                                               uu____11281)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11323),
                                                          (a2,uu____11325))
                                                           ->
                                                           let uu____11350 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11350
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11209
                                                uu____11231
                                               in
                                            match uu____11202 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___174_11376 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___174_11376.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___174_11376.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11392 =
                                                  solve env1 wl'  in
                                                (match uu____11392 with
                                                 | Success (uu____11395,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___175_11399
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___175_11399.attempting);
                                                            wl_deferred =
                                                              (uu___175_11399.wl_deferred);
                                                            ctr =
                                                              (uu___175_11399.ctr);
                                                            defer_ok =
                                                              (uu___175_11399.defer_ok);
                                                            smt_ok =
                                                              (uu___175_11399.smt_ok);
                                                            tcenv =
                                                              (uu___175_11399.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11408 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11440 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11440 with
                                | (t1_base,p1_opt) ->
                                    let uu____11487 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11487 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11597 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11597
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
                                               let uu____11645 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11645
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
                                               let uu____11675 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11675
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
                                               let uu____11705 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11705
                                           | uu____11708 -> t_base  in
                                         let uu____11725 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11725 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11739 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11739, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11746 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11746 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11793 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11793 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11840 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11840
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
                              let uu____11864 = combine t11 t21 wl2  in
                              (match uu____11864 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11897 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11897
                                     then
                                       let uu____11898 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11898
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11937 ts1 =
               match uu____11937 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12000 = pairwise out t wl2  in
                        (match uu____12000 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12036 =
               let uu____12047 = FStar_List.hd ts  in (uu____12047, [], wl1)
                in
             let uu____12056 = FStar_List.tl ts  in
             aux uu____12036 uu____12056  in
           let uu____12063 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12063 with
           | (this_flex,this_rigid) ->
               let uu____12087 =
                 let uu____12088 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12088.FStar_Syntax_Syntax.n  in
               (match uu____12087 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12109 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12109
                    then
                      let uu____12110 = destruct_flex_t this_flex wl  in
                      (match uu____12110 with
                       | (flex,wl1) ->
                           let uu____12117 = quasi_pattern env flex  in
                           (match uu____12117 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12135 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12135
                                  then
                                    let uu____12136 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12136
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12139 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___176_12142 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___176_12142.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___176_12142.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___176_12142.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___176_12142.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___176_12142.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___176_12142.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___176_12142.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___176_12142.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___176_12142.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12139)
                | uu____12143 ->
                    ((let uu____12145 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12145
                      then
                        let uu____12146 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12146
                      else ());
                     (let uu____12148 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12148 with
                      | (u,_args) ->
                          let uu____12185 =
                            let uu____12186 = FStar_Syntax_Subst.compress u
                               in
                            uu____12186.FStar_Syntax_Syntax.n  in
                          (match uu____12185 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12217 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12217 with
                                 | (u',uu____12233) ->
                                     let uu____12254 =
                                       let uu____12255 = whnf env u'  in
                                       uu____12255.FStar_Syntax_Syntax.n  in
                                     (match uu____12254 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12280 -> false)
                                  in
                               let uu____12281 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___142_12304  ->
                                         match uu___142_12304 with
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
                                              | uu____12313 -> false)
                                         | uu____12316 -> false))
                                  in
                               (match uu____12281 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12330 = whnf env this_rigid
                                         in
                                      let uu____12331 =
                                        FStar_List.collect
                                          (fun uu___143_12337  ->
                                             match uu___143_12337 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12343 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12343]
                                             | uu____12345 -> [])
                                          bounds_probs
                                         in
                                      uu____12330 :: uu____12331  in
                                    let uu____12346 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12346 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12377 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12392 =
                                               let uu____12393 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12393.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12392 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12405 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12405)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12414 -> bound  in
                                           let uu____12415 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12415)  in
                                         (match uu____12377 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12444 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12444
                                                then
                                                  let wl'1 =
                                                    let uu___177_12446 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___177_12446.wl_deferred);
                                                      ctr =
                                                        (uu___177_12446.ctr);
                                                      defer_ok =
                                                        (uu___177_12446.defer_ok);
                                                      smt_ok =
                                                        (uu___177_12446.smt_ok);
                                                      tcenv =
                                                        (uu___177_12446.tcenv);
                                                      wl_implicits =
                                                        (uu___177_12446.wl_implicits)
                                                    }  in
                                                  let uu____12447 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12447
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12450 =
                                                  solve_t env eq_prob
                                                    (let uu___178_12452 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___178_12452.wl_deferred);
                                                       ctr =
                                                         (uu___178_12452.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___178_12452.smt_ok);
                                                       tcenv =
                                                         (uu___178_12452.tcenv);
                                                       wl_implicits =
                                                         (uu___178_12452.wl_implicits)
                                                     })
                                                   in
                                                match uu____12450 with
                                                | Success uu____12453 ->
                                                    let wl2 =
                                                      let uu___179_12459 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___179_12459.wl_deferred);
                                                        ctr =
                                                          (uu___179_12459.ctr);
                                                        defer_ok =
                                                          (uu___179_12459.defer_ok);
                                                        smt_ok =
                                                          (uu___179_12459.smt_ok);
                                                        tcenv =
                                                          (uu___179_12459.tcenv);
                                                        wl_implicits =
                                                          (uu___179_12459.wl_implicits)
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
                                                    let uu____12474 =
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
                                                     (let uu____12486 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12486
                                                      then
                                                        let uu____12487 =
                                                          let uu____12488 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12488
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12487
                                                      else ());
                                                     (let uu____12494 =
                                                        let uu____12509 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12509)
                                                         in
                                                      match uu____12494 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12531))
                                                          ->
                                                          let uu____12556 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12556
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
                                                                 let uu____12573
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12573)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          let uu____12597 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12597
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
                                                                   let uu____12615
                                                                    =
                                                                    let uu____12620
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12620
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12615
                                                                    [] wl2
                                                                    in
                                                                 let uu____12625
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12625)))
                                                      | uu____12626 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12641 when flip ->
                               let uu____12642 =
                                 let uu____12643 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12644 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12643 uu____12644
                                  in
                               failwith uu____12642
                           | uu____12645 ->
                               let uu____12646 =
                                 let uu____12647 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12648 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12647 uu____12648
                                  in
                               failwith uu____12646)))))

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
                      (fun uu____12676  ->
                         match uu____12676 with
                         | (x,i) ->
                             let uu____12687 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12687, i)) bs_lhs
                     in
                  let uu____12688 = lhs  in
                  match uu____12688 with
                  | (uu____12689,u_lhs,uu____12691) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12804 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12814 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12814, univ)
                             in
                          match uu____12804 with
                          | (k,univ) ->
                              let uu____12823 =
                                let uu____12830 =
                                  let uu____12833 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12833
                                   in
                                copy_uvar u_lhs uu____12830 wl2  in
                              (match uu____12823 with
                               | (uu____12846,u,wl3) ->
                                   let uu____12849 =
                                     let uu____12852 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12852
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12849, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12888 =
                              let uu____12901 =
                                let uu____12910 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12910 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12956  ->
                                   fun uu____12957  ->
                                     match (uu____12956, uu____12957) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13048 =
                                           let uu____13055 =
                                             let uu____13058 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13058
                                              in
                                           copy_uvar u_lhs uu____13055 wl2
                                            in
                                         (match uu____13048 with
                                          | (uu____13081,t_a,wl3) ->
                                              let uu____13084 =
                                                let uu____13091 =
                                                  let uu____13094 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____13094
                                                   in
                                                copy_uvar u_lhs uu____13091
                                                  wl3
                                                 in
                                              (match uu____13084 with
                                               | (uu____13109,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12901
                                ([], wl1)
                               in
                            (match uu____12888 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___180_13170 = ct  in
                                   let uu____13171 =
                                     let uu____13174 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13174
                                      in
                                   let uu____13189 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___180_13170.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___180_13170.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13171;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13189;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___180_13170.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___181_13207 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___181_13207.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___181_13207.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13210 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13210 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13264 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13264 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13281 =
                                          let uu____13286 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13286)  in
                                        TERM uu____13281  in
                                      let uu____13287 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13287 with
                                       | (sub_prob,wl3) ->
                                           let uu____13298 =
                                             let uu____13299 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13299
                                              in
                                           solve env uu____13298))
                             | (x,imp)::formals2 ->
                                 let uu____13313 =
                                   let uu____13320 =
                                     let uu____13323 =
                                       let uu____13326 =
                                         let uu____13327 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13327
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13326
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13323
                                      in
                                   copy_uvar u_lhs uu____13320 wl1  in
                                 (match uu____13313 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13351 =
                                          let uu____13354 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13354
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13351 t_y
                                         in
                                      let uu____13355 =
                                        let uu____13358 =
                                          let uu____13361 =
                                            let uu____13362 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13362, imp)  in
                                          [uu____13361]  in
                                        FStar_List.append bs_terms
                                          uu____13358
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13355 formals2 wl2)
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
              (let uu____13404 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13404
               then
                 let uu____13405 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13406 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13405 (rel_to_string (p_rel orig)) uu____13406
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13511 = rhs wl1 scope env1 subst1  in
                     (match uu____13511 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13531 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13531
                            then
                              let uu____13532 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13532
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___182_13586 = hd1  in
                       let uu____13587 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_13586.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_13586.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13587
                       }  in
                     let hd21 =
                       let uu___183_13591 = hd2  in
                       let uu____13592 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___183_13591.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___183_13591.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13592
                       }  in
                     let uu____13595 =
                       let uu____13600 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13600
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13595 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13619 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13619
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13623 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13623 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13678 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13678
                                  in
                               ((let uu____13690 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13690
                                 then
                                   let uu____13691 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13692 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13691
                                     uu____13692
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13719 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13748 = aux wl [] env [] bs1 bs2  in
               match uu____13748 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13795 = attempt sub_probs wl2  in
                   solve env uu____13795)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13800 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13800 wl)

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
              let uu____13814 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13814 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13844 = lhs1  in
              match uu____13844 with
              | (uu____13847,ctx_u,uu____13849) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13855 ->
                        let uu____13856 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13856 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13903 = quasi_pattern env1 lhs1  in
              match uu____13903 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13933) ->
                  let uu____13938 = lhs1  in
                  (match uu____13938 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13952 = occurs_check ctx_u rhs1  in
                       (match uu____13952 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13994 =
                                let uu____14001 =
                                  let uu____14002 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14002
                                   in
                                FStar_Util.Inl uu____14001  in
                              (uu____13994, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14022 =
                                 let uu____14023 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14023  in
                               if uu____14022
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14043 =
                                    let uu____14050 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14050  in
                                  let uu____14055 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14043, uu____14055)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14117  ->
                     match uu____14117 with
                     | (x,i) ->
                         let uu____14128 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14128, i)) bs_lhs
                 in
              let uu____14129 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14129 with
              | (rhs_hd,args) ->
                  let uu____14166 = FStar_Util.prefix args  in
                  (match uu____14166 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14224 = lhs1  in
                       (match uu____14224 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14228 =
                              let uu____14239 =
                                let uu____14246 =
                                  let uu____14249 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14249
                                   in
                                copy_uvar u_lhs uu____14246 wl1  in
                              match uu____14239 with
                              | (uu____14270,t_last_arg,wl2) ->
                                  let uu____14273 =
                                    let uu____14280 =
                                      let uu____14283 =
                                        let uu____14290 =
                                          let uu____14297 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14297]  in
                                        FStar_List.append bs_lhs uu____14290
                                         in
                                      let uu____14314 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14283
                                        uu____14314
                                       in
                                    copy_uvar u_lhs uu____14280 wl2  in
                                  (match uu____14273 with
                                   | (uu____14327,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14333 =
                                         let uu____14340 =
                                           let uu____14343 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14343
                                            in
                                         copy_uvar u_lhs uu____14340 wl3  in
                                       (match uu____14333 with
                                        | (uu____14356,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14228 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14380 =
                                     let uu____14381 =
                                       let uu____14386 =
                                         let uu____14387 =
                                           let uu____14390 =
                                             let uu____14395 =
                                               let uu____14396 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14396]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14395
                                              in
                                           uu____14390
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14387
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14386)  in
                                     TERM uu____14381  in
                                   [uu____14380]  in
                                 let uu____14417 =
                                   let uu____14424 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14424 with
                                   | (p1,wl3) ->
                                       let uu____14441 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14441 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14417 with
                                  | (sub_probs,wl3) ->
                                      let uu____14468 =
                                        let uu____14469 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14469  in
                                      solve env1 uu____14468))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14502 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14502 with
                | (uu____14517,args) ->
                    (match args with | [] -> false | uu____14545 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14560 =
                  let uu____14561 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14561.FStar_Syntax_Syntax.n  in
                match uu____14560 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14564 -> true
                | uu____14577 -> false  in
              let uu____14578 = quasi_pattern env1 lhs1  in
              match uu____14578 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14589 =
                    let uu____14590 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14590
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14589
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14597 = is_app rhs1  in
                  if uu____14597
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14599 = is_arrow rhs1  in
                     if uu____14599
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14601 =
                          let uu____14602 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14602
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14601))
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
                let uu____14605 = lhs  in
                (match uu____14605 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14609 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14609 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14624 =
                              let uu____14627 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14627
                               in
                            FStar_All.pipe_right uu____14624
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14642 = occurs_check ctx_uv rhs1  in
                          (match uu____14642 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14664 =
                                   let uu____14665 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14665
                                    in
                                 giveup_or_defer env orig wl uu____14664
                               else
                                 (let uu____14667 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14667
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14672 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14672
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14674 =
                                         let uu____14675 =
                                           names_to_string1 fvs2  in
                                         let uu____14676 =
                                           names_to_string1 fvs1  in
                                         let uu____14677 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14675 uu____14676
                                           uu____14677
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14674)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14683 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14687 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14687 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14710 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14710
                             | (FStar_Util.Inl msg,uu____14712) ->
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
                  (let uu____14741 =
                     let uu____14758 = quasi_pattern env lhs  in
                     let uu____14765 = quasi_pattern env rhs  in
                     (uu____14758, uu____14765)  in
                   match uu____14741 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14808 = lhs  in
                       (match uu____14808 with
                        | ({ FStar_Syntax_Syntax.n = uu____14809;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14811;_},u_lhs,uu____14813)
                            ->
                            let uu____14816 = rhs  in
                            (match uu____14816 with
                             | (uu____14817,u_rhs,uu____14819) ->
                                 let uu____14820 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14820
                                 then
                                   let uu____14821 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14821
                                 else
                                   (let uu____14823 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14823 with
                                    | (sub_prob,wl1) ->
                                        let uu____14834 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14834 with
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
                                             let uu____14862 =
                                               let uu____14869 =
                                                 let uu____14872 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14872
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
                                                 uu____14869
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14862 with
                                              | (uu____14875,w,wl2) ->
                                                  let w_app =
                                                    let uu____14881 =
                                                      let uu____14886 =
                                                        FStar_List.map
                                                          (fun uu____14895 
                                                             ->
                                                             match uu____14895
                                                             with
                                                             | (z,uu____14901)
                                                                 ->
                                                                 let uu____14902
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14902)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14886
                                                       in
                                                    uu____14881
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14906 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14906
                                                    then
                                                      let uu____14907 =
                                                        let uu____14910 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14911 =
                                                          let uu____14914 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14915 =
                                                            let uu____14918 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14919 =
                                                              let uu____14922
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14927
                                                                =
                                                                let uu____14930
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14935
                                                                  =
                                                                  let uu____14938
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14938]
                                                                   in
                                                                uu____14930
                                                                  ::
                                                                  uu____14935
                                                                 in
                                                              uu____14922 ::
                                                                uu____14927
                                                               in
                                                            uu____14918 ::
                                                              uu____14919
                                                             in
                                                          uu____14914 ::
                                                            uu____14915
                                                           in
                                                        uu____14910 ::
                                                          uu____14911
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14907
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14944 =
                                                          let uu____14949 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14949)
                                                           in
                                                        TERM uu____14944  in
                                                      let uu____14950 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14950
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14955 =
                                                             let uu____14960
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
                                                               uu____14960)
                                                              in
                                                           TERM uu____14955
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14961 =
                                                      let uu____14962 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14962
                                                       in
                                                    solve env uu____14961)))))))
                   | uu____14963 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15027 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15027
            then
              let uu____15028 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15029 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15030 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15031 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15028 uu____15029 uu____15030 uu____15031
            else ());
           (let uu____15035 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15035
            then
              let uu____15036 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15037 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15038 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15039 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____15036 uu____15037 uu____15038 uu____15039
            else ());
           (let uu____15041 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15041 with
            | (head1,args1) ->
                let uu____15078 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15078 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15132 =
                         let uu____15133 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15134 = args_to_string args1  in
                         let uu____15135 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15136 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15133 uu____15134 uu____15135 uu____15136
                          in
                       giveup env1 uu____15132 orig
                     else
                       (let uu____15138 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15144 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15144 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15138
                        then
                          let uu____15145 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15145 with
                          | USolved wl2 ->
                              let uu____15147 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15147
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15151 = base_and_refinement env1 t1  in
                           match uu____15151 with
                           | (base1,refinement1) ->
                               let uu____15176 = base_and_refinement env1 t2
                                  in
                               (match uu____15176 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15233 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15233 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15237 =
                                                FStar_List.fold_right2
                                                  (fun uu____15270  ->
                                                     fun uu____15271  ->
                                                       fun uu____15272  ->
                                                         match (uu____15270,
                                                                 uu____15271,
                                                                 uu____15272)
                                                         with
                                                         | ((a,uu____15308),
                                                            (a',uu____15310),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15331
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15331
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15237 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15359 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15359
                                                     then
                                                       let uu____15360 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15360
                                                     else ());
                                                    FStar_List.iter
                                                      (def_check_prob
                                                         "solve_t' subprobs")
                                                      subprobs;
                                                    (let formula =
                                                       let uu____15366 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15366
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     let uu____15374 =
                                                       attempt subprobs wl4
                                                        in
                                                     solve env1 uu____15374))))
                                     | uu____15375 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___184_15415 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___184_15415.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___184_15415.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___184_15415.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___184_15415.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___184_15415.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___184_15415.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___184_15415.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___184_15415.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15453 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15453
            then
              let uu____15454 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15455 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15456 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15457 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15454 uu____15455 uu____15456 uu____15457
            else ());
           (let uu____15459 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15459 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15490,uu____15491) ->
                     let rec may_relate head3 =
                       let uu____15518 =
                         let uu____15519 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15519.FStar_Syntax_Syntax.n  in
                       match uu____15518 with
                       | FStar_Syntax_Syntax.Tm_name uu____15522 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15523 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15546;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15547;
                             FStar_Syntax_Syntax.fv_qual = uu____15548;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15551;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15552;
                             FStar_Syntax_Syntax.fv_qual = uu____15553;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15557,uu____15558) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15600) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15606) ->
                           may_relate t
                       | uu____15611 -> false  in
                     let uu____15612 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15612
                     then
                       let uu____15613 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15613 with
                        | (guard,wl2) ->
                            let uu____15620 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15620)
                     else
                       (let uu____15622 =
                          let uu____15623 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15624 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15623 uu____15624
                           in
                        giveup env1 uu____15622 orig)
                 | (HeadMatch (true ),uu____15625) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15638 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15638 with
                        | (guard,wl2) ->
                            let uu____15645 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15645)
                     else
                       (let uu____15647 =
                          let uu____15648 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15649 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15648 uu____15649
                           in
                        giveup env1 uu____15647 orig)
                 | (uu____15650,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___185_15664 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___185_15664.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___185_15664.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___185_15664.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___185_15664.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___185_15664.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___185_15664.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___185_15664.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___185_15664.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15688 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15688
          then
            let uu____15689 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15689
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15694 =
                let uu____15697 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15697  in
              def_check_closed_in (p_loc orig) "ref.t1" uu____15694 t1);
             (let uu____15709 =
                let uu____15712 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15712  in
              def_check_closed_in (p_loc orig) "ref.t2" uu____15709 t2);
             (let uu____15724 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15724
              then
                let uu____15725 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15726 =
                  let uu____15727 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15728 =
                    let uu____15729 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15729  in
                  Prims.strcat uu____15727 uu____15728  in
                let uu____15730 =
                  let uu____15731 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15732 =
                    let uu____15733 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15733  in
                  Prims.strcat uu____15731 uu____15732  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15725
                  uu____15726 uu____15730
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15736,uu____15737) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15762,FStar_Syntax_Syntax.Tm_delayed uu____15763) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15788,uu____15789) ->
                  let uu____15816 =
                    let uu___186_15817 = problem  in
                    let uu____15818 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15817.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15818;
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15817.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___186_15817.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___186_15817.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15817.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15817.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15817.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15817.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15817.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15816 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15819,uu____15820) ->
                  let uu____15827 =
                    let uu___187_15828 = problem  in
                    let uu____15829 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15828.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15829;
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15828.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___187_15828.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___187_15828.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15828.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15828.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15828.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15828.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15828.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15827 wl
              | (uu____15830,FStar_Syntax_Syntax.Tm_ascribed uu____15831) ->
                  let uu____15858 =
                    let uu___188_15859 = problem  in
                    let uu____15860 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15859.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___188_15859.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15859.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15860;
                      FStar_TypeChecker_Common.element =
                        (uu___188_15859.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15859.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15859.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15859.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15859.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15859.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15858 wl
              | (uu____15861,FStar_Syntax_Syntax.Tm_meta uu____15862) ->
                  let uu____15869 =
                    let uu___189_15870 = problem  in
                    let uu____15871 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15870.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___189_15870.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15870.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15871;
                      FStar_TypeChecker_Common.element =
                        (uu___189_15870.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15870.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15870.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15870.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15870.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15870.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15869 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15873),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15875)) ->
                  let uu____15884 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15884
              | (FStar_Syntax_Syntax.Tm_bvar uu____15885,uu____15886) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15887,FStar_Syntax_Syntax.Tm_bvar uu____15888) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___144_15947 =
                    match uu___144_15947 with
                    | [] -> c
                    | bs ->
                        let uu____15969 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15969
                     in
                  let uu____15978 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15978 with
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
                                    let uu____16101 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____16101
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
                  let mk_t t l uu___145_16176 =
                    match uu___145_16176 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16210 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16210 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16329 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16330 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16329
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16330 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16331,uu____16332) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16359 -> true
                    | uu____16376 -> false  in
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
                      (let uu____16429 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16437 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16437.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16437.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16437.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16437.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16437.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16437.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16437.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16437.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16437.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16437.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16437.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16437.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16437.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16437.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16437.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16437.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16437.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16437.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16437.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16437.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16437.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16437.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16437.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16437.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16437.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16437.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16437.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16437.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16437.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16437.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16437.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16437.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16437.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16437.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16437.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16437.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16429 with
                       | (uu____16440,ty,uu____16442) ->
                           let uu____16443 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16443)
                     in
                  let uu____16444 =
                    let uu____16461 = maybe_eta t1  in
                    let uu____16468 = maybe_eta t2  in
                    (uu____16461, uu____16468)  in
                  (match uu____16444 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16510 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16510.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16510.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16510.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16510.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16510.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16510.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16510.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16510.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16531 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16531
                       then
                         let uu____16532 = destruct_flex_t not_abs wl  in
                         (match uu____16532 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16547 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16547.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16547.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16547.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16547.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16547.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16547.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16547.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16547.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16569 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16569
                       then
                         let uu____16570 = destruct_flex_t not_abs wl  in
                         (match uu____16570 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16585 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16585.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16585.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16585.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16585.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16585.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16585.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16585.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16585.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16587 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16604,FStar_Syntax_Syntax.Tm_abs uu____16605) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16632 -> true
                    | uu____16649 -> false  in
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
                      (let uu____16702 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16710 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16710.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16710.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16710.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16710.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16710.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16710.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16710.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16710.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16710.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16710.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16710.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16710.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16710.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16710.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16710.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16710.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16710.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16710.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16710.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16710.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16710.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16710.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16710.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16710.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16710.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16710.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16710.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16710.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16710.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16710.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16710.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16710.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16710.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16710.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16710.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16710.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16702 with
                       | (uu____16713,ty,uu____16715) ->
                           let uu____16716 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16716)
                     in
                  let uu____16717 =
                    let uu____16734 = maybe_eta t1  in
                    let uu____16741 = maybe_eta t2  in
                    (uu____16734, uu____16741)  in
                  (match uu____16717 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16783 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16783.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16783.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16783.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16783.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16783.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16783.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16783.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16783.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16804 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16804
                       then
                         let uu____16805 = destruct_flex_t not_abs wl  in
                         (match uu____16805 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16820 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16820.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16820.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16820.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16820.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16820.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16820.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16820.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16820.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16842 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16842
                       then
                         let uu____16843 = destruct_flex_t not_abs wl  in
                         (match uu____16843 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16858 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16858.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16858.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16858.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16858.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16858.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16858.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16858.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16858.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16860 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16892 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16892) &&
                       (let uu____16896 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16896))
                      &&
                      (let uu____16903 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16903 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___146_16915 =
                             match uu___146_16915 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16916 -> true
                             | uu____16917 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16918 -> false)
                     in
                  let uu____16919 = as_refinement should_delta env wl t1  in
                  (match uu____16919 with
                   | (x11,phi1) ->
                       let uu____16932 = as_refinement should_delta env wl t2
                          in
                       (match uu____16932 with
                        | (x21,phi21) ->
                            let uu____16945 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16945 with
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
                                   let uu____17011 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____17011
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____17023 =
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
                                   (let uu____17034 =
                                      let uu____17037 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____17037
                                       in
                                    def_check_closed_in (p_loc orig) "ref.1"
                                      uu____17034 (p_guard base_prob));
                                   (let uu____17049 =
                                      let uu____17052 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____17052
                                       in
                                    def_check_closed_in (p_loc orig) "ref.2"
                                      uu____17049 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____17064 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____17064)
                                    in
                                 let has_uvars =
                                   (let uu____17068 =
                                      let uu____17069 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____17069  in
                                    Prims.op_Negation uu____17068) ||
                                     (let uu____17073 =
                                        let uu____17074 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____17074
                                         in
                                      Prims.op_Negation uu____17073)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____17077 =
                                     let uu____17082 =
                                       let uu____17089 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____17089]  in
                                     mk_t_problem wl1 uu____17082 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____17077 with
                                    | (ref_prob,wl2) ->
                                        let uu____17104 =
                                          solve env1
                                            (let uu___193_17106 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___193_17106.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___193_17106.smt_ok);
                                               tcenv = (uu___193_17106.tcenv);
                                               wl_implicits =
                                                 (uu___193_17106.wl_implicits)
                                             })
                                           in
                                        (match uu____17104 with
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
                                         | Success uu____17116 ->
                                             let guard =
                                               let uu____17124 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____17124
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___194_17133 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___194_17133.attempting);
                                                 wl_deferred =
                                                   (uu___194_17133.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___194_17133.defer_ok);
                                                 smt_ok =
                                                   (uu___194_17133.smt_ok);
                                                 tcenv =
                                                   (uu___194_17133.tcenv);
                                                 wl_implicits =
                                                   (uu___194_17133.wl_implicits)
                                               }  in
                                             let uu____17134 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____17134))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17136,FStar_Syntax_Syntax.Tm_uvar uu____17137) ->
                  let uu____17166 = destruct_flex_t t1 wl  in
                  (match uu____17166 with
                   | (f1,wl1) ->
                       let uu____17173 = destruct_flex_t t2 wl1  in
                       (match uu____17173 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17180;
                    FStar_Syntax_Syntax.pos = uu____17181;
                    FStar_Syntax_Syntax.vars = uu____17182;_},uu____17183),FStar_Syntax_Syntax.Tm_uvar
                 uu____17184) ->
                  let uu____17233 = destruct_flex_t t1 wl  in
                  (match uu____17233 with
                   | (f1,wl1) ->
                       let uu____17240 = destruct_flex_t t2 wl1  in
                       (match uu____17240 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17247,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17248;
                    FStar_Syntax_Syntax.pos = uu____17249;
                    FStar_Syntax_Syntax.vars = uu____17250;_},uu____17251))
                  ->
                  let uu____17300 = destruct_flex_t t1 wl  in
                  (match uu____17300 with
                   | (f1,wl1) ->
                       let uu____17307 = destruct_flex_t t2 wl1  in
                       (match uu____17307 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17314;
                    FStar_Syntax_Syntax.pos = uu____17315;
                    FStar_Syntax_Syntax.vars = uu____17316;_},uu____17317),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17318;
                    FStar_Syntax_Syntax.pos = uu____17319;
                    FStar_Syntax_Syntax.vars = uu____17320;_},uu____17321))
                  ->
                  let uu____17390 = destruct_flex_t t1 wl  in
                  (match uu____17390 with
                   | (f1,wl1) ->
                       let uu____17397 = destruct_flex_t t2 wl1  in
                       (match uu____17397 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17404,uu____17405) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17420 = destruct_flex_t t1 wl  in
                  (match uu____17420 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17427;
                    FStar_Syntax_Syntax.pos = uu____17428;
                    FStar_Syntax_Syntax.vars = uu____17429;_},uu____17430),uu____17431)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17466 = destruct_flex_t t1 wl  in
                  (match uu____17466 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17473,FStar_Syntax_Syntax.Tm_uvar uu____17474) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17489,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17490;
                    FStar_Syntax_Syntax.pos = uu____17491;
                    FStar_Syntax_Syntax.vars = uu____17492;_},uu____17493))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17528,FStar_Syntax_Syntax.Tm_arrow uu____17529) ->
                  solve_t' env
                    (let uu___195_17557 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17557.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17557.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17557.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17557.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17557.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17557.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17557.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17557.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17557.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17558;
                    FStar_Syntax_Syntax.pos = uu____17559;
                    FStar_Syntax_Syntax.vars = uu____17560;_},uu____17561),FStar_Syntax_Syntax.Tm_arrow
                 uu____17562) ->
                  solve_t' env
                    (let uu___195_17610 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17610.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17610.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17610.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17610.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17610.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17610.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17610.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17610.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17610.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17611,FStar_Syntax_Syntax.Tm_uvar uu____17612) ->
                  let uu____17627 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17627
              | (uu____17628,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17629;
                    FStar_Syntax_Syntax.pos = uu____17630;
                    FStar_Syntax_Syntax.vars = uu____17631;_},uu____17632))
                  ->
                  let uu____17667 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17667
              | (FStar_Syntax_Syntax.Tm_uvar uu____17668,uu____17669) ->
                  let uu____17684 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17684
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17685;
                    FStar_Syntax_Syntax.pos = uu____17686;
                    FStar_Syntax_Syntax.vars = uu____17687;_},uu____17688),uu____17689)
                  ->
                  let uu____17724 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17724
              | (FStar_Syntax_Syntax.Tm_refine uu____17725,uu____17726) ->
                  let t21 =
                    let uu____17734 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17734  in
                  solve_t env
                    (let uu___196_17760 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___196_17760.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___196_17760.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___196_17760.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___196_17760.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___196_17760.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___196_17760.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___196_17760.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___196_17760.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___196_17760.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17761,FStar_Syntax_Syntax.Tm_refine uu____17762) ->
                  let t11 =
                    let uu____17770 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17770  in
                  solve_t env
                    (let uu___197_17796 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_17796.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_17796.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_17796.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_17796.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_17796.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___197_17796.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_17796.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_17796.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_17796.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17878 =
                    let uu____17879 = guard_of_prob env wl problem t1 t2  in
                    match uu____17879 with
                    | (guard,wl1) ->
                        let uu____17886 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17886
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____18097 = br1  in
                        (match uu____18097 with
                         | (p1,w1,uu____18122) ->
                             let uu____18139 = br2  in
                             (match uu____18139 with
                              | (p2,w2,uu____18158) ->
                                  let uu____18163 =
                                    let uu____18164 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____18164  in
                                  if uu____18163
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____18180 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____18180 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18213 = br2  in
                                         (match uu____18213 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18248 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18248
                                                 in
                                              let uu____18259 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18282,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18299) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18342 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18342 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18259
                                                (fun uu____18384  ->
                                                   match uu____18384 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18405 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18405
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18420 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18420
                                                              (fun
                                                                 uu____18444 
                                                                 ->
                                                                 match uu____18444
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18529 -> FStar_Pervasives_Native.None  in
                  let uu____18566 = solve_branches wl brs1 brs2  in
                  (match uu____18566 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18594 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18594 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18611 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18611  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18620 =
                              let uu____18621 =
                                attempt sub_probs1
                                  (let uu___198_18623 = wl3  in
                                   {
                                     attempting = (uu___198_18623.attempting);
                                     wl_deferred =
                                       (uu___198_18623.wl_deferred);
                                     ctr = (uu___198_18623.ctr);
                                     defer_ok = (uu___198_18623.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___198_18623.tcenv);
                                     wl_implicits =
                                       (uu___198_18623.wl_implicits)
                                   })
                                 in
                              solve env uu____18621  in
                            (match uu____18620 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18627 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18633,uu____18634) ->
                  let head1 =
                    let uu____18658 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18658
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18698 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18698
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18738 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18738
                    then
                      let uu____18739 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18740 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18741 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18739 uu____18740 uu____18741
                    else ());
                   (let uu____18743 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18743
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18750 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18750
                       then
                         let uu____18751 =
                           let uu____18758 =
                             let uu____18759 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18759 = FStar_Syntax_Util.Equal  in
                           if uu____18758
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18769 = mk_eq2 wl orig t1 t2  in
                              match uu____18769 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18751 with
                         | (guard,wl1) ->
                             let uu____18790 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18790
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18793,uu____18794) ->
                  let head1 =
                    let uu____18802 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18802
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18842 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18842
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18882 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18882
                    then
                      let uu____18883 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18884 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18885 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18883 uu____18884 uu____18885
                    else ());
                   (let uu____18887 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18887
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18894 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18894
                       then
                         let uu____18895 =
                           let uu____18902 =
                             let uu____18903 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18903 = FStar_Syntax_Util.Equal  in
                           if uu____18902
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18913 = mk_eq2 wl orig t1 t2  in
                              match uu____18913 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18895 with
                         | (guard,wl1) ->
                             let uu____18934 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18934
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18937,uu____18938) ->
                  let head1 =
                    let uu____18940 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18940
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18980 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18980
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19020 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19020
                    then
                      let uu____19021 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19022 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19023 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19021 uu____19022 uu____19023
                    else ());
                   (let uu____19025 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19025
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19032 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19032
                       then
                         let uu____19033 =
                           let uu____19040 =
                             let uu____19041 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19041 = FStar_Syntax_Util.Equal  in
                           if uu____19040
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19051 = mk_eq2 wl orig t1 t2  in
                              match uu____19051 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19033 with
                         | (guard,wl1) ->
                             let uu____19072 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19072
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____19075,uu____19076) ->
                  let head1 =
                    let uu____19078 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19078
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19118 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19118
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19158 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19158
                    then
                      let uu____19159 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19160 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19161 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19159 uu____19160 uu____19161
                    else ());
                   (let uu____19163 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19163
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19170 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19170
                       then
                         let uu____19171 =
                           let uu____19178 =
                             let uu____19179 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19179 = FStar_Syntax_Util.Equal  in
                           if uu____19178
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19189 = mk_eq2 wl orig t1 t2  in
                              match uu____19189 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19171 with
                         | (guard,wl1) ->
                             let uu____19210 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19210
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____19213,uu____19214) ->
                  let head1 =
                    let uu____19216 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19216
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19256 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19256
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19296 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19296
                    then
                      let uu____19297 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19298 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19299 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19297 uu____19298 uu____19299
                    else ());
                   (let uu____19301 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19301
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19308 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19308
                       then
                         let uu____19309 =
                           let uu____19316 =
                             let uu____19317 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19317 = FStar_Syntax_Util.Equal  in
                           if uu____19316
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19327 = mk_eq2 wl orig t1 t2  in
                              match uu____19327 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19309 with
                         | (guard,wl1) ->
                             let uu____19348 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19348
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19351,uu____19352) ->
                  let head1 =
                    let uu____19368 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19368
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19408 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19408
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19448 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19448
                    then
                      let uu____19449 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19450 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19451 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19449 uu____19450 uu____19451
                    else ());
                   (let uu____19453 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19453
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19460 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19460
                       then
                         let uu____19461 =
                           let uu____19468 =
                             let uu____19469 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19469 = FStar_Syntax_Util.Equal  in
                           if uu____19468
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19479 = mk_eq2 wl orig t1 t2  in
                              match uu____19479 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19461 with
                         | (guard,wl1) ->
                             let uu____19500 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19500
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19503,FStar_Syntax_Syntax.Tm_match uu____19504) ->
                  let head1 =
                    let uu____19528 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19528
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19568 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19568
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19608 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19608
                    then
                      let uu____19609 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19610 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19611 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19609 uu____19610 uu____19611
                    else ());
                   (let uu____19613 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19613
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19620 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19620
                       then
                         let uu____19621 =
                           let uu____19628 =
                             let uu____19629 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19629 = FStar_Syntax_Util.Equal  in
                           if uu____19628
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19639 = mk_eq2 wl orig t1 t2  in
                              match uu____19639 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19621 with
                         | (guard,wl1) ->
                             let uu____19660 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19660
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19663,FStar_Syntax_Syntax.Tm_uinst uu____19664) ->
                  let head1 =
                    let uu____19672 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19672
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19712 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19712
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19752 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19752
                    then
                      let uu____19753 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19754 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19755 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19753 uu____19754 uu____19755
                    else ());
                   (let uu____19757 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19757
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19764 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19764
                       then
                         let uu____19765 =
                           let uu____19772 =
                             let uu____19773 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19773 = FStar_Syntax_Util.Equal  in
                           if uu____19772
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19783 = mk_eq2 wl orig t1 t2  in
                              match uu____19783 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19765 with
                         | (guard,wl1) ->
                             let uu____19804 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19804
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19807,FStar_Syntax_Syntax.Tm_name uu____19808) ->
                  let head1 =
                    let uu____19810 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19810
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19850 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19850
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19890 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19890
                    then
                      let uu____19891 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19892 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19893 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19891 uu____19892 uu____19893
                    else ());
                   (let uu____19895 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19895
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19902 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19902
                       then
                         let uu____19903 =
                           let uu____19910 =
                             let uu____19911 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19911 = FStar_Syntax_Util.Equal  in
                           if uu____19910
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19921 = mk_eq2 wl orig t1 t2  in
                              match uu____19921 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19903 with
                         | (guard,wl1) ->
                             let uu____19942 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19942
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19945,FStar_Syntax_Syntax.Tm_constant uu____19946) ->
                  let head1 =
                    let uu____19948 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19948
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19982 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19982
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20016 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20016
                    then
                      let uu____20017 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20018 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20019 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20017 uu____20018 uu____20019
                    else ());
                   (let uu____20021 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20021
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20028 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20028
                       then
                         let uu____20029 =
                           let uu____20036 =
                             let uu____20037 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20037 = FStar_Syntax_Util.Equal  in
                           if uu____20036
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20047 = mk_eq2 wl orig t1 t2  in
                              match uu____20047 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20029 with
                         | (guard,wl1) ->
                             let uu____20068 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20068
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20071,FStar_Syntax_Syntax.Tm_fvar uu____20072) ->
                  let head1 =
                    let uu____20074 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20074
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20108 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20108
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20142 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20142
                    then
                      let uu____20143 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20144 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20145 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20143 uu____20144 uu____20145
                    else ());
                   (let uu____20147 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20147
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20154 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20154
                       then
                         let uu____20155 =
                           let uu____20162 =
                             let uu____20163 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20163 = FStar_Syntax_Util.Equal  in
                           if uu____20162
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20173 = mk_eq2 wl orig t1 t2  in
                              match uu____20173 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20155 with
                         | (guard,wl1) ->
                             let uu____20194 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20194
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20197,FStar_Syntax_Syntax.Tm_app uu____20198) ->
                  let head1 =
                    let uu____20214 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20214
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20248 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20248
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20288 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20288
                    then
                      let uu____20289 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20290 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20291 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20289 uu____20290 uu____20291
                    else ());
                   (let uu____20293 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20293
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20300 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20300
                       then
                         let uu____20301 =
                           let uu____20308 =
                             let uu____20309 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20309 = FStar_Syntax_Util.Equal  in
                           if uu____20308
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20319 = mk_eq2 wl orig t1 t2  in
                              match uu____20319 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20301 with
                         | (guard,wl1) ->
                             let uu____20340 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20340
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20343,FStar_Syntax_Syntax.Tm_let uu____20344) ->
                  let uu____20369 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20369
                  then
                    let uu____20370 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20370
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20372,uu____20373) ->
                  let uu____20386 =
                    let uu____20391 =
                      let uu____20392 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20393 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20394 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20395 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20392 uu____20393 uu____20394 uu____20395
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20391)
                     in
                  FStar_Errors.raise_error uu____20386
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20396,FStar_Syntax_Syntax.Tm_let uu____20397) ->
                  let uu____20410 =
                    let uu____20415 =
                      let uu____20416 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20417 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20418 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20419 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20416 uu____20417 uu____20418 uu____20419
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20415)
                     in
                  FStar_Errors.raise_error uu____20410
                    t1.FStar_Syntax_Syntax.pos
              | uu____20420 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20479 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20479
           then
             let uu____20480 =
               let uu____20481 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20481  in
             let uu____20482 =
               let uu____20483 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20483  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20480 uu____20482
           else ());
          (let uu____20485 =
             let uu____20486 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20486  in
           if uu____20485
           then
             let uu____20487 =
               let uu____20488 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20489 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20488 uu____20489
                in
             giveup env uu____20487 orig
           else
             (let uu____20491 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20491 with
              | (ret_sub_prob,wl1) ->
                  let uu____20498 =
                    FStar_List.fold_right2
                      (fun uu____20531  ->
                         fun uu____20532  ->
                           fun uu____20533  ->
                             match (uu____20531, uu____20532, uu____20533)
                             with
                             | ((a1,uu____20569),(a2,uu____20571),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20592 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20592 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20498 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20621 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20621  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____20629 = attempt sub_probs wl3  in
                       solve env uu____20629)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20652 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20655)::[] -> wp1
              | uu____20672 ->
                  let uu____20681 =
                    let uu____20682 =
                      let uu____20683 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20683  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20682
                     in
                  failwith uu____20681
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20689 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20689]
              | x -> x  in
            let uu____20691 =
              let uu____20700 =
                let uu____20707 =
                  let uu____20708 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20708 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20707  in
              [uu____20700]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20691;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20721 = lift_c1 ()  in solve_eq uu____20721 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___147_20727  ->
                       match uu___147_20727 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20728 -> false))
                in
             let uu____20729 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20755)::uu____20756,(wp2,uu____20758)::uu____20759)
                   -> (wp1, wp2)
               | uu____20812 ->
                   let uu____20833 =
                     let uu____20838 =
                       let uu____20839 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20840 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20839 uu____20840
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20838)
                      in
                   FStar_Errors.raise_error uu____20833
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20729 with
             | (wpc1,wpc2) ->
                 let uu____20847 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20847
                 then
                   let uu____20850 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20850 wl
                 else
                   (let uu____20852 =
                      let uu____20859 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20859  in
                    match uu____20852 with
                    | (c2_decl,qualifiers) ->
                        let uu____20880 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20880
                        then
                          let c1_repr =
                            let uu____20884 =
                              let uu____20885 =
                                let uu____20886 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20886  in
                              let uu____20887 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20885 uu____20887
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20884
                             in
                          let c2_repr =
                            let uu____20889 =
                              let uu____20890 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20891 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20890 uu____20891
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20889
                             in
                          let uu____20892 =
                            let uu____20897 =
                              let uu____20898 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20899 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20898 uu____20899
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20897
                             in
                          (match uu____20892 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____20903 = attempt [prob] wl2  in
                               solve env uu____20903)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20914 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20914
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20917 =
                                     let uu____20924 =
                                       let uu____20925 =
                                         let uu____20940 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20943 =
                                           let uu____20952 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20959 =
                                             let uu____20968 =
                                               let uu____20975 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20975
                                                in
                                             [uu____20968]  in
                                           uu____20952 :: uu____20959  in
                                         (uu____20940, uu____20943)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20925
                                        in
                                     FStar_Syntax_Syntax.mk uu____20924  in
                                   uu____20917 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21016 =
                                    let uu____21023 =
                                      let uu____21024 =
                                        let uu____21039 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21042 =
                                          let uu____21051 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21058 =
                                            let uu____21067 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21074 =
                                              let uu____21083 =
                                                let uu____21090 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21090
                                                 in
                                              [uu____21083]  in
                                            uu____21067 :: uu____21074  in
                                          uu____21051 :: uu____21058  in
                                        (uu____21039, uu____21042)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21024
                                       in
                                    FStar_Syntax_Syntax.mk uu____21023  in
                                  uu____21016 FStar_Pervasives_Native.None r)
                              in
                           let uu____21134 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____21134 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____21142 =
                                   let uu____21145 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____21145
                                    in
                                 solve_prob orig uu____21142 [] wl1  in
                               let uu____21148 = attempt [base_prob] wl2  in
                               solve env uu____21148)))
           in
        let uu____21149 = FStar_Util.physical_equality c1 c2  in
        if uu____21149
        then
          let uu____21150 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21150
        else
          ((let uu____21153 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21153
            then
              let uu____21154 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21155 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21154
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21155
            else ());
           (let uu____21157 =
              let uu____21166 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21169 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21166, uu____21169)  in
            match uu____21157 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21187),FStar_Syntax_Syntax.Total
                    (t2,uu____21189)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21206 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21206 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21207,FStar_Syntax_Syntax.Total uu____21208) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21226),FStar_Syntax_Syntax.Total
                    (t2,uu____21228)) ->
                     let uu____21245 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21245 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21247),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21249)) ->
                     let uu____21266 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21266 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21268),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21270)) ->
                     let uu____21287 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21287 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21288,FStar_Syntax_Syntax.Comp uu____21289) ->
                     let uu____21298 =
                       let uu___199_21301 = problem  in
                       let uu____21304 =
                         let uu____21305 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21305
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21301.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21304;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21301.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21301.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21301.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21301.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21301.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21301.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21301.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21301.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21298 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21306,FStar_Syntax_Syntax.Comp uu____21307) ->
                     let uu____21316 =
                       let uu___199_21319 = problem  in
                       let uu____21322 =
                         let uu____21323 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21323
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21319.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21322;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21319.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21319.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21319.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21319.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21319.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21319.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21319.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21319.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21316 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21324,FStar_Syntax_Syntax.GTotal uu____21325) ->
                     let uu____21334 =
                       let uu___200_21337 = problem  in
                       let uu____21340 =
                         let uu____21341 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21341
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21337.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21337.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21337.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21340;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21337.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21337.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21337.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21337.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21337.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21337.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21334 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21342,FStar_Syntax_Syntax.Total uu____21343) ->
                     let uu____21352 =
                       let uu___200_21355 = problem  in
                       let uu____21358 =
                         let uu____21359 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21359
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21355.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21355.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21355.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21358;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21355.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21355.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21355.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21355.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21355.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21355.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21352 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21360,FStar_Syntax_Syntax.Comp uu____21361) ->
                     let uu____21362 =
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
                     if uu____21362
                     then
                       let uu____21363 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21363 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21367 =
                            let uu____21372 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21372
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21378 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21379 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21378, uu____21379))
                             in
                          match uu____21367 with
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
                           (let uu____21386 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21386
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21388 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21388 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21391 =
                                  let uu____21392 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21393 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21392 uu____21393
                                   in
                                giveup env uu____21391 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21400 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21428  ->
              match uu____21428 with
              | (uu____21437,tm,uu____21439,uu____21440) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21400 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21473 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21473 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21491 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21519  ->
                match uu____21519 with
                | (u1,u2) ->
                    let uu____21526 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21527 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21526 uu____21527))
         in
      FStar_All.pipe_right uu____21491 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21554,[])) -> "{}"
      | uu____21579 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21602 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21602
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21605 =
              FStar_List.map
                (fun uu____21615  ->
                   match uu____21615 with
                   | (uu____21620,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21605 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21625 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21625 imps
  
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
                  let uu____21678 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21678
                  then
                    let uu____21679 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21680 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21679
                      (rel_to_string rel) uu____21680
                  else "TOP"  in
                let uu____21682 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21682 with
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
              let uu____21740 =
                let uu____21743 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21743
                 in
              FStar_Syntax_Syntax.new_bv uu____21740 t1  in
            let uu____21746 =
              let uu____21751 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21751
               in
            match uu____21746 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21824 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21824
              then
                let uu____21825 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21825
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
          ((let uu____21847 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21847
            then
              let uu____21848 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21848
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21852 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21852
             then
               let uu____21853 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21853
             else ());
            (let f2 =
               let uu____21856 =
                 let uu____21857 = FStar_Syntax_Util.unmeta f1  in
                 uu____21857.FStar_Syntax_Syntax.n  in
               match uu____21856 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21861 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___201_21862 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___201_21862.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___201_21862.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___201_21862.FStar_TypeChecker_Env.implicits)
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
            let uu____21964 =
              let uu____21965 =
                let uu____21966 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21966;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21965  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21964
  
let with_guard_no_simp :
  'Auu____21981 .
    'Auu____21981 ->
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
            let uu____22004 =
              let uu____22005 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22005;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22004
  
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
          (let uu____22043 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22043
           then
             let uu____22044 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22045 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22044
               uu____22045
           else ());
          (let uu____22047 =
             let uu____22052 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____22052
              in
           match uu____22047 with
           | (prob,wl) ->
               let g =
                 let uu____22060 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____22078  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____22060  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22120 = try_teq true env t1 t2  in
        match uu____22120 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22124 = FStar_TypeChecker_Env.get_range env  in
              let uu____22125 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22124 uu____22125);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22132 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22132
              then
                let uu____22133 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22134 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22135 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22133
                  uu____22134 uu____22135
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
          let uu____22157 = FStar_TypeChecker_Env.get_range env  in
          let uu____22158 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22157 uu____22158
  
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
        (let uu____22183 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22183
         then
           let uu____22184 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22185 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____22184 uu____22185
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____22188 =
           let uu____22195 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____22195 "sub_comp"
            in
         match uu____22188 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____22206 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____22224  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____22206)))
  
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
      fun uu____22277  ->
        match uu____22277 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22320 =
                 let uu____22325 =
                   let uu____22326 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22327 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22326 uu____22327
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22325)  in
               let uu____22328 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22320 uu____22328)
               in
            let equiv1 v1 v' =
              let uu____22340 =
                let uu____22345 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22346 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22345, uu____22346)  in
              match uu____22340 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22365 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22395 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22395 with
                      | FStar_Syntax_Syntax.U_unif uu____22402 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22431  ->
                                    match uu____22431 with
                                    | (u,v') ->
                                        let uu____22440 = equiv1 v1 v'  in
                                        if uu____22440
                                        then
                                          let uu____22443 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22443 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22459 -> []))
               in
            let uu____22464 =
              let wl =
                let uu___202_22468 = empty_worklist env  in
                {
                  attempting = (uu___202_22468.attempting);
                  wl_deferred = (uu___202_22468.wl_deferred);
                  ctr = (uu___202_22468.ctr);
                  defer_ok = false;
                  smt_ok = (uu___202_22468.smt_ok);
                  tcenv = (uu___202_22468.tcenv);
                  wl_implicits = (uu___202_22468.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22486  ->
                      match uu____22486 with
                      | (lb,v1) ->
                          let uu____22493 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22493 with
                           | USolved wl1 -> ()
                           | uu____22495 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22505 =
              match uu____22505 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22514) -> true
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
                      uu____22537,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22539,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22550) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22557,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22565 -> false)
               in
            let uu____22570 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22585  ->
                      match uu____22585 with
                      | (u,v1) ->
                          let uu____22592 = check_ineq (u, v1)  in
                          if uu____22592
                          then true
                          else
                            ((let uu____22595 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22595
                              then
                                let uu____22596 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22597 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22596
                                  uu____22597
                              else ());
                             false)))
               in
            if uu____22570
            then ()
            else
              ((let uu____22601 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22601
                then
                  ((let uu____22603 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22603);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22613 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22613))
                else ());
               (let uu____22623 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22623))
  
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
        let fail1 uu____22690 =
          match uu____22690 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___203_22711 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___203_22711.attempting);
            wl_deferred = (uu___203_22711.wl_deferred);
            ctr = (uu___203_22711.ctr);
            defer_ok;
            smt_ok = (uu___203_22711.smt_ok);
            tcenv = (uu___203_22711.tcenv);
            wl_implicits = (uu___203_22711.wl_implicits)
          }  in
        (let uu____22713 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22713
         then
           let uu____22714 = FStar_Util.string_of_bool defer_ok  in
           let uu____22715 = wl_to_string wl  in
           let uu____22716 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22714 uu____22715 uu____22716
         else ());
        (let g1 =
           let uu____22727 = solve_and_commit env wl fail1  in
           match uu____22727 with
           | FStar_Pervasives_Native.Some
               (uu____22734::uu____22735,uu____22736) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___204_22761 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___204_22761.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___204_22761.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22770 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___205_22778 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___205_22778.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___205_22778.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___205_22778.FStar_TypeChecker_Env.implicits)
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
    let uu____22826 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22826 with
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
            let uu___206_22949 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___206_22949.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___206_22949.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___206_22949.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22950 =
            let uu____22951 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22951  in
          if uu____22950
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22959 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22960 =
                       let uu____22961 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22961
                        in
                     FStar_Errors.diag uu____22959 uu____22960)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22965 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22966 =
                        let uu____22967 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22967
                         in
                      FStar_Errors.diag uu____22965 uu____22966)
                   else ();
                   (let uu____22970 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22970 "discharge_guard'"
                      env vc1);
                   (let uu____22971 = check_trivial vc1  in
                    match uu____22971 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22978 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22979 =
                                let uu____22980 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22980
                                 in
                              FStar_Errors.diag uu____22978 uu____22979)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22985 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22986 =
                                let uu____22987 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22987
                                 in
                              FStar_Errors.diag uu____22985 uu____22986)
                           else ();
                           (let vcs =
                              let uu____23000 = FStar_Options.use_tactics ()
                                 in
                              if uu____23000
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23022  ->
                                     (let uu____23024 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____23024);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____23067  ->
                                              match uu____23067 with
                                              | (env1,goal,opts) ->
                                                  let uu____23083 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____23083, opts)))))
                              else
                                (let uu____23085 =
                                   let uu____23094 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23094)  in
                                 [uu____23085])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23137  ->
                                    match uu____23137 with
                                    | (env1,goal,opts) ->
                                        let uu____23153 = check_trivial goal
                                           in
                                        (match uu____23153 with
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
                                                (let uu____23161 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23162 =
                                                   let uu____23163 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____23164 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23163 uu____23164
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23161 uu____23162)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23167 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23168 =
                                                   let uu____23169 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23169
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23167 uu____23168)
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
      let uu____23183 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23183 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23190 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23190
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23201 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23201 with
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
            let uu____23234 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23234 with
            | FStar_Pervasives_Native.Some uu____23237 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23257 = acc  in
            match uu____23257 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23309 = hd1  in
                     (match uu____23309 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23323 = unresolved ctx_u  in
                             if uu____23323
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___207_23335 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___207_23335.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___207_23335.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___207_23335.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___207_23335.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___207_23335.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___207_23335.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___207_23335.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___207_23335.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___207_23335.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___207_23335.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___207_23335.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___207_23335.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___207_23335.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___207_23335.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___207_23335.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___207_23335.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___207_23335.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___207_23335.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___207_23335.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___207_23335.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___207_23335.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___207_23335.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___207_23335.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___207_23335.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___207_23335.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___207_23335.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___207_23335.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___207_23335.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___207_23335.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___207_23335.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___207_23335.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___207_23335.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___207_23335.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___207_23335.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___207_23335.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___207_23335.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___207_23335.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___207_23335.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___208_23338 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___208_23338.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___208_23338.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___208_23338.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___208_23338.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___208_23338.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___208_23338.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___208_23338.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___208_23338.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___208_23338.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___208_23338.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___208_23338.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___208_23338.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___208_23338.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___208_23338.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___208_23338.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___208_23338.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___208_23338.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___208_23338.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___208_23338.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___208_23338.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___208_23338.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___208_23338.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___208_23338.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___208_23338.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___208_23338.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___208_23338.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___208_23338.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___208_23338.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___208_23338.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___208_23338.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___208_23338.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___208_23338.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___208_23338.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23341 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23341
                                   then
                                     let uu____23342 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23343 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23344 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23345 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23342 uu____23343 uu____23344
                                       reason uu____23345
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23356 =
                                             let uu____23365 =
                                               let uu____23372 =
                                                 let uu____23373 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23374 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23375 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23373 uu____23374
                                                   uu____23375
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23372, r)
                                                in
                                             [uu____23365]  in
                                           FStar_Errors.add_errors
                                             uu____23356);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___211_23389 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___211_23389.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___211_23389.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___211_23389.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23392 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23402  ->
                                               let uu____23403 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23404 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23405 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23403 uu____23404
                                                 reason uu____23405)) env2 g2
                                         true
                                        in
                                     match uu____23392 with
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
          let uu___212_23415 = g  in
          let uu____23416 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___212_23415.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___212_23415.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___212_23415.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23416
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
        let uu____23466 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23466 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23475 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23475
      | (reason,e,ctx_u,r)::uu____23480 ->
          let uu____23499 =
            let uu____23504 =
              let uu____23505 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23506 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23505 uu____23506 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23504)
             in
          FStar_Errors.raise_error uu____23499 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___213_23517 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___213_23517.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___213_23517.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___213_23517.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23532 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23532 with
      | FStar_Pervasives_Native.Some uu____23538 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23554 = try_teq false env t1 t2  in
        match uu____23554 with
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
        (let uu____23588 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23588
         then
           let uu____23589 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23590 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23589
             uu____23590
         else ());
        (let uu____23592 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23592 with
         | (prob,x,wl) ->
             let g =
               let uu____23611 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23629  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23611  in
             ((let uu____23657 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23657
               then
                 let uu____23658 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23659 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23660 =
                   let uu____23661 = FStar_Util.must g  in
                   guard_to_string env uu____23661  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23658 uu____23659 uu____23660
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
        let uu____23695 = check_subtyping env t1 t2  in
        match uu____23695 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23714 =
              let uu____23715 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23715 g  in
            FStar_Pervasives_Native.Some uu____23714
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23733 = check_subtyping env t1 t2  in
        match uu____23733 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23752 =
              let uu____23753 =
                let uu____23754 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23754]  in
              close_guard env uu____23753 g  in
            FStar_Pervasives_Native.Some uu____23752
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23783 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23783
         then
           let uu____23784 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23785 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23784
             uu____23785
         else ());
        (let uu____23787 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23787 with
         | (prob,x,wl) ->
             let g =
               let uu____23800 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23818  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23800  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23847 =
                      let uu____23848 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23848]  in
                    close_guard env uu____23847 g1  in
                  discharge_guard_nosmt env g2))
  