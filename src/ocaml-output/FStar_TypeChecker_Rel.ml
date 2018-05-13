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
      FStar_Syntax_Syntax.binders ->
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
                  let env = FStar_TypeChecker_Env.push_binders wl.tcenv scope
                     in
                  let uu____2167 =
                    let uu____2174 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      env.FStar_TypeChecker_Env.gamma uu____2174
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2167 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2193 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2193;
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
                  (let uu____2249 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2249 with
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
                  (let uu____2316 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2316 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2352 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2352 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2352 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2352 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2403 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2440 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2440]  in
                        let uu____2453 =
                          let uu____2456 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2456  in
                        let uu____2459 =
                          let uu____2462 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2462  in
                        (bs, uu____2453, uu____2459)
                     in
                  match uu____2403 with
                  | (bs,lg_ty,elt) ->
                      let uu____2484 =
                        let uu____2491 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___161_2499 = wl  in
                           {
                             attempting = (uu___161_2499.attempting);
                             wl_deferred = (uu___161_2499.wl_deferred);
                             ctr = (uu___161_2499.ctr);
                             defer_ok = (uu___161_2499.defer_ok);
                             smt_ok = (uu___161_2499.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___161_2499.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2491
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2484 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2511 =
                                   let uu____2516 =
                                     let uu____2517 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2517]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2516
                                    in
                                 uu____2511 FStar_Pervasives_Native.None loc
                              in
                           let prob =
                             let uu____2541 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2541;
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
                let uu____2583 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2583;
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
  'Auu____2595 .
    worklist ->
      'Auu____2595 FStar_TypeChecker_Common.problem ->
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
        let uu____2645 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2645
        then
          let uu____2646 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2647 = prob_to_string env d  in
          let uu____2648 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2646 uu____2647 uu____2648 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2654 -> failwith "impossible"  in
           let uu____2655 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2667 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2668 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2667, uu____2668)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2672 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2673 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2672, uu____2673)
              in
           match uu____2655 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___130_2691  ->
            match uu___130_2691 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2703 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2707 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  def_check_closed_in t.FStar_Syntax_Syntax.pos "commit"
                    uu____2707 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___131_2732  ->
           match uu___131_2732 with
           | UNIV uu____2735 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2742 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2742
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
        (fun uu___132_2766  ->
           match uu___132_2766 with
           | UNIV (u',t) ->
               let uu____2771 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2771
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2775 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2786 =
        let uu____2787 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2787
         in
      FStar_Syntax_Subst.compress uu____2786
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2798 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2798
  
let norm_arg :
  'Auu____2805 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2805) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2805)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2828 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2828, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2869  ->
              match uu____2869 with
              | (x,imp) ->
                  let uu____2880 =
                    let uu___162_2881 = x  in
                    let uu____2882 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___162_2881.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___162_2881.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2882
                    }  in
                  (uu____2880, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2903 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2903
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2907 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2907
        | uu____2910 -> u2  in
      let uu____2911 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2911
  
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
                (let uu____3033 = norm_refinement env t12  in
                 match uu____3033 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3050;
                     FStar_Syntax_Syntax.vars = uu____3051;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3077 =
                       let uu____3078 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3079 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3078 uu____3079
                        in
                     failwith uu____3077)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3095 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3095
          | FStar_Syntax_Syntax.Tm_uinst uu____3096 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3135 =
                   let uu____3136 = FStar_Syntax_Subst.compress t1'  in
                   uu____3136.FStar_Syntax_Syntax.n  in
                 match uu____3135 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3153 -> aux true t1'
                 | uu____3160 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3177 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3210 =
                   let uu____3211 = FStar_Syntax_Subst.compress t1'  in
                   uu____3211.FStar_Syntax_Syntax.n  in
                 match uu____3210 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3228 -> aux true t1'
                 | uu____3235 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3252 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3299 =
                   let uu____3300 = FStar_Syntax_Subst.compress t1'  in
                   uu____3300.FStar_Syntax_Syntax.n  in
                 match uu____3299 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3317 -> aux true t1'
                 | uu____3324 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3341 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3358 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3375 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3392 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3409 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3438 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3471 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3494 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3525 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3554 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3593 ->
              let uu____3600 =
                let uu____3601 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3602 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3601 uu____3602
                 in
              failwith uu____3600
          | FStar_Syntax_Syntax.Tm_ascribed uu____3617 ->
              let uu____3644 =
                let uu____3645 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3646 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3645 uu____3646
                 in
              failwith uu____3644
          | FStar_Syntax_Syntax.Tm_delayed uu____3661 ->
              let uu____3686 =
                let uu____3687 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3688 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3687 uu____3688
                 in
              failwith uu____3686
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3703 =
                let uu____3704 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3705 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3704 uu____3705
                 in
              failwith uu____3703
           in
        let uu____3720 = whnf env t1  in aux false uu____3720
  
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
      let uu____3766 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3766 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3802 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3802, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3813 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3813 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3840 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3840 with
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
  fun uu____3927  ->
    match uu____3927 with
    | (t_base,refopt) ->
        let uu____3960 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3960 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4000 =
      let uu____4003 =
        let uu____4006 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4029  ->
                  match uu____4029 with | (uu____4036,uu____4037,x) -> x))
           in
        FStar_List.append wl.attempting uu____4006  in
      FStar_List.map (wl_prob_to_string wl) uu____4003  in
    FStar_All.pipe_right uu____4000 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4051 .
    ('Auu____4051,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4062  ->
    match uu____4062 with
    | (uu____4069,c,args) ->
        let uu____4072 = print_ctx_uvar c  in
        let uu____4073 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4072 uu____4073
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4079 = FStar_Syntax_Util.head_and_args t  in
    match uu____4079 with
    | (head1,_args) ->
        let uu____4116 =
          let uu____4117 = FStar_Syntax_Subst.compress head1  in
          uu____4117.FStar_Syntax_Syntax.n  in
        (match uu____4116 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4120 -> true
         | uu____4135 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4141 = FStar_Syntax_Util.head_and_args t  in
    match uu____4141 with
    | (head1,_args) ->
        let uu____4178 =
          let uu____4179 = FStar_Syntax_Subst.compress head1  in
          uu____4179.FStar_Syntax_Syntax.n  in
        (match uu____4178 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4183) -> u
         | uu____4204 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4227 = FStar_Syntax_Util.head_and_args t  in
      match uu____4227 with
      | (head1,args) ->
          let uu____4268 =
            let uu____4269 = FStar_Syntax_Subst.compress head1  in
            uu____4269.FStar_Syntax_Syntax.n  in
          (match uu____4268 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4277)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4320 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___133_4345  ->
                         match uu___133_4345 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4349 =
                               let uu____4350 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4350.FStar_Syntax_Syntax.n  in
                             (match uu____4349 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4354 -> false)
                         | uu____4355 -> true))
                  in
               (match uu____4320 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4377 =
                        FStar_List.collect
                          (fun uu___134_4387  ->
                             match uu___134_4387 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4391 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4391]
                             | uu____4392 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4377 FStar_List.rev  in
                    let uu____4409 =
                      let uu____4416 =
                        let uu____4423 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___135_4441  ->
                                  match uu___135_4441 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4445 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4445]
                                  | uu____4446 -> []))
                           in
                        FStar_All.pipe_right uu____4423 FStar_List.rev  in
                      let uu____4463 =
                        let uu____4466 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4466  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4416 uu____4463
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4409 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4495  ->
                                match uu____4495 with
                                | (x,i) ->
                                    let uu____4506 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4506, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4529  ->
                                match uu____4529 with
                                | (a,i) ->
                                    let uu____4540 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4540, i)) args_sol
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
           | uu____4556 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4576 =
          let uu____4597 =
            let uu____4598 = FStar_Syntax_Subst.compress k  in
            uu____4598.FStar_Syntax_Syntax.n  in
          match uu____4597 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4667 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4667)
              else
                (let uu____4697 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4697 with
                 | (ys',t1,uu____4728) ->
                     let uu____4733 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4733))
          | uu____4766 ->
              let uu____4767 =
                let uu____4772 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4772)  in
              ((ys, t), uu____4767)
           in
        match uu____4576 with
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
                 let uu____4849 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4849 c  in
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
               (let uu____4923 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4923
                then
                  let uu____4924 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4925 = print_ctx_uvar uv  in
                  let uu____4926 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4924 uu____4925 uu____4926
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4932 =
                   let uu____4933 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4933  in
                 let uu____4934 =
                   let uu____4937 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4937
                    in
                 def_check_closed_in (p_loc prob) uu____4932 uu____4934 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uu____4956 = p_guard_uvar prob  in
             match uu____4956 with
             | (xs,uv) ->
                 let fail1 uu____4968 =
                   let uu____4969 =
                     let uu____4970 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4971 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4970 uu____4971
                      in
                   failwith uu____4969  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____5021  ->
                           match uu____5021 with
                           | (a,i) ->
                               let uu____5034 =
                                 let uu____5035 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____5035.FStar_Syntax_Syntax.n  in
                               (match uu____5034 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____5053 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____5061 =
                     let uu____5062 = is_flex g  in
                     Prims.op_Negation uu____5062  in
                   if uu____5061
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5066 = destruct_flex_t g wl  in
                      match uu____5066 with
                      | ((uu____5071,uv1,args),wl1) ->
                          ((let uu____5076 = args_as_binders args  in
                            assign_solution uu____5076 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___163_5078 = wl1  in
                   {
                     attempting = (uu___163_5078.attempting);
                     wl_deferred = (uu___163_5078.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___163_5078.defer_ok);
                     smt_ok = (uu___163_5078.smt_ok);
                     tcenv = (uu___163_5078.tcenv);
                     wl_implicits = (uu___163_5078.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5099 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5099
         then
           let uu____5100 = FStar_Util.string_of_int pid  in
           let uu____5101 =
             let uu____5102 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5102 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5100 uu____5101
         else ());
        commit sol;
        (let uu___164_5109 = wl  in
         {
           attempting = (uu___164_5109.attempting);
           wl_deferred = (uu___164_5109.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___164_5109.defer_ok);
           smt_ok = (uu___164_5109.smt_ok);
           tcenv = (uu___164_5109.tcenv);
           wl_implicits = (uu___164_5109.wl_implicits)
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
             | (uu____5171,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5199 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5199
              in
           (let uu____5205 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5205
            then
              let uu____5206 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5207 =
                let uu____5208 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5208 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5206 uu____5207
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
        let uu____5233 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5233 FStar_Util.set_elements  in
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
      let uu____5267 = occurs uk t  in
      match uu____5267 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5296 =
                 let uu____5297 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5298 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5297 uu____5298
                  in
               FStar_Pervasives_Native.Some uu____5296)
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
            let uu____5387 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5387 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5431 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5479  ->
             match uu____5479 with
             | (x,uu____5489) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5502 = FStar_List.last bs  in
      match uu____5502 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5520) ->
          let uu____5525 =
            FStar_Util.prefix_until
              (fun uu___136_5540  ->
                 match uu___136_5540 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5542 -> false) g
             in
          (match uu____5525 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5555,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5591 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5591 with
        | (pfx,uu____5601) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5613 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5613 with
             | (uu____5620,src',wl1) ->
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
                 | uu____5720 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5721 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5775  ->
                  fun uu____5776  ->
                    match (uu____5775, uu____5776) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5857 =
                          let uu____5858 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5858
                           in
                        if uu____5857
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5883 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5883
                           then
                             let uu____5896 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5896)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5721 with | (isect,uu____5933) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5962 'Auu____5963 .
    (FStar_Syntax_Syntax.bv,'Auu____5962) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5963) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6020  ->
              fun uu____6021  ->
                match (uu____6020, uu____6021) with
                | ((a,uu____6039),(b,uu____6041)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6056 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6056) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6086  ->
           match uu____6086 with
           | (y,uu____6092) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6101 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6101) FStar_Pervasives_Native.tuple2
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
                   let uu____6231 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6231
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6251 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6294 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6332 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6345 -> false
  
let string_of_option :
  'Auu____6352 .
    ('Auu____6352 -> Prims.string) ->
      'Auu____6352 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___137_6367  ->
      match uu___137_6367 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6373 = f x  in Prims.strcat "Some " uu____6373
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___138_6378  ->
    match uu___138_6378 with
    | MisMatch (d1,d2) ->
        let uu____6389 =
          let uu____6390 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6391 =
            let uu____6392 =
              let uu____6393 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6393 ")"  in
            Prims.strcat ") (" uu____6392  in
          Prims.strcat uu____6390 uu____6391  in
        Prims.strcat "MisMatch (" uu____6389
    | HeadMatch u ->
        let uu____6395 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6395
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___139_6400  ->
    match uu___139_6400 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6415 -> HeadMatch false
  
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
          let uu____6429 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6429 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6440 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6463 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6472 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6500 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6500
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6501 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6502 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6503 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6518 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6531 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6555) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6561,uu____6562) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6604) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6625;
             FStar_Syntax_Syntax.index = uu____6626;
             FStar_Syntax_Syntax.sort = t2;_},uu____6628)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6635 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6636 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6637 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6650 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6657 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6675 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6675
  
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
            let uu____6702 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6702
            then FullMatch
            else
              (let uu____6704 =
                 let uu____6713 =
                   let uu____6716 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6716  in
                 let uu____6717 =
                   let uu____6720 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6720  in
                 (uu____6713, uu____6717)  in
               MisMatch uu____6704)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6726),FStar_Syntax_Syntax.Tm_uinst (g,uu____6728)) ->
            let uu____6737 = head_matches env f g  in
            FStar_All.pipe_right uu____6737 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6740 = FStar_Const.eq_const c d  in
            if uu____6740
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6747),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6749)) ->
            let uu____6790 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6790
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6797),FStar_Syntax_Syntax.Tm_refine (y,uu____6799)) ->
            let uu____6808 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6808 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6810),uu____6811) ->
            let uu____6816 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6816 head_match
        | (uu____6817,FStar_Syntax_Syntax.Tm_refine (x,uu____6819)) ->
            let uu____6824 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6824 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6825,FStar_Syntax_Syntax.Tm_type
           uu____6826) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6827,FStar_Syntax_Syntax.Tm_arrow uu____6828) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6854),FStar_Syntax_Syntax.Tm_app (head',uu____6856))
            ->
            let uu____6897 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6897 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6899),uu____6900) ->
            let uu____6921 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6921 head_match
        | (uu____6922,FStar_Syntax_Syntax.Tm_app (head1,uu____6924)) ->
            let uu____6945 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6945 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6946,FStar_Syntax_Syntax.Tm_let
           uu____6947) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6972,FStar_Syntax_Syntax.Tm_match uu____6973) ->
            HeadMatch true
        | uu____7018 ->
            let uu____7023 =
              let uu____7032 = delta_depth_of_term env t11  in
              let uu____7035 = delta_depth_of_term env t21  in
              (uu____7032, uu____7035)  in
            MisMatch uu____7023
  
let head_matches_delta :
  'Auu____7052 .
    FStar_TypeChecker_Env.env ->
      'Auu____7052 ->
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
            (let uu____7101 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7101
             then
               let uu____7102 = FStar_Syntax_Print.term_to_string t  in
               let uu____7103 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7102 uu____7103
             else ());
            (let uu____7105 =
               let uu____7106 = FStar_Syntax_Util.un_uinst head1  in
               uu____7106.FStar_Syntax_Syntax.n  in
             match uu____7105 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7112 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7112 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7126 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7126
                        then
                          let uu____7127 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7127
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7129 ->
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
                      ((let uu____7140 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7140
                        then
                          let uu____7141 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7142 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7141
                            uu____7142
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7144 -> FStar_Pervasives_Native.None)
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
            (let uu____7282 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7282
             then
               let uu____7283 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7284 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7285 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7283
                 uu____7284 uu____7285
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7309 =
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
               match uu____7309 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7354 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7354 with
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
                  uu____7386),uu____7387)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7405 =
                      let uu____7414 = maybe_inline t11  in
                      let uu____7417 = maybe_inline t21  in
                      (uu____7414, uu____7417)  in
                    match uu____7405 with
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
                 (uu____7454,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7455))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7473 =
                      let uu____7482 = maybe_inline t11  in
                      let uu____7485 = maybe_inline t21  in
                      (uu____7482, uu____7485)  in
                    match uu____7473 with
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
             | MisMatch uu____7534 -> fail1 n_delta r t11 t21
             | uu____7543 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7556 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7556
           then
             let uu____7557 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7558 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7559 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7566 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7584 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7584
                    (fun uu____7618  ->
                       match uu____7618 with
                       | (t11,t21) ->
                           let uu____7625 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7626 =
                             let uu____7627 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7627  in
                           Prims.strcat uu____7625 uu____7626))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7557 uu____7558 uu____7559 uu____7566
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7639 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7639 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___140_7652  ->
    match uu___140_7652 with
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
      let uu___165_7689 = p  in
      let uu____7692 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7693 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___165_7689.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7692;
        FStar_TypeChecker_Common.relation =
          (uu___165_7689.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7693;
        FStar_TypeChecker_Common.element =
          (uu___165_7689.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___165_7689.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___165_7689.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___165_7689.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___165_7689.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___165_7689.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7707 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7707
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7712 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7734 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7734 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7742 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7742 with
           | (lh,lhs_args) ->
               let uu____7783 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7783 with
                | (rh,rhs_args) ->
                    let uu____7824 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7837,FStar_Syntax_Syntax.Tm_uvar uu____7838)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7919 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7942,uu____7943)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7960,FStar_Syntax_Syntax.Tm_uvar uu____7961)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7978,FStar_Syntax_Syntax.Tm_arrow uu____7979)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8009 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8009.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8009.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8009.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8009.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8009.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8009.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8009.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8009.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8009.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8012,FStar_Syntax_Syntax.Tm_type uu____8013)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8031 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8031.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8031.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8031.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8031.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8031.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8031.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8031.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8031.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8031.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8034,FStar_Syntax_Syntax.Tm_uvar uu____8035)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8053 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8053.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8053.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8053.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8053.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8053.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8053.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8053.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8053.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8053.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8056,FStar_Syntax_Syntax.Tm_uvar uu____8057)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8074,uu____8075)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8092,FStar_Syntax_Syntax.Tm_uvar uu____8093)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8110,uu____8111) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7824 with
                     | (rank,tp1) ->
                         let uu____8124 =
                           FStar_All.pipe_right
                             (let uu___167_8128 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___167_8128.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___167_8128.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___167_8128.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___167_8128.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___167_8128.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___167_8128.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___167_8128.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___167_8128.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___167_8128.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8124))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8134 =
            FStar_All.pipe_right
              (let uu___168_8138 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___168_8138.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___168_8138.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___168_8138.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___168_8138.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___168_8138.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___168_8138.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___168_8138.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___168_8138.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___168_8138.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8134)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8199 probs =
      match uu____8199 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8280 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8301 = rank wl.tcenv hd1  in
               (match uu____8301 with
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
                      (let uu____8360 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8364 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8364)
                          in
                       if uu____8360
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
          let uu____8432 = FStar_Syntax_Util.head_and_args t  in
          match uu____8432 with
          | (hd1,uu____8448) ->
              let uu____8469 =
                let uu____8470 = FStar_Syntax_Subst.compress hd1  in
                uu____8470.FStar_Syntax_Syntax.n  in
              (match uu____8469 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8474) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8508  ->
                           match uu____8508 with
                           | (y,uu____8514) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8528  ->
                                       match uu____8528 with
                                       | (x,uu____8534) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8535 -> false)
           in
        let uu____8536 = rank tcenv p  in
        match uu____8536 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8543 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8570 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8584 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8598 -> false
  
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
                        let uu____8650 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8650 with
                        | (k,uu____8656) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8666 -> false)))
            | uu____8667 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8719 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8725 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8725 = (Prims.parse_int "0")))
                           in
                        if uu____8719 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8741 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8747 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8747 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8741)
               in
            let uu____8748 = filter1 u12  in
            let uu____8751 = filter1 u22  in (uu____8748, uu____8751)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8780 = filter_out_common_univs us1 us2  in
                (match uu____8780 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8839 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8839 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8842 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8852 =
                          let uu____8853 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8854 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8853
                            uu____8854
                           in
                        UFailed uu____8852))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8878 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8878 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8904 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8904 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8907 ->
                let uu____8912 =
                  let uu____8913 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8914 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8913
                    uu____8914 msg
                   in
                UFailed uu____8912
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8915,uu____8916) ->
              let uu____8917 =
                let uu____8918 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8919 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8918 uu____8919
                 in
              failwith uu____8917
          | (FStar_Syntax_Syntax.U_unknown ,uu____8920) ->
              let uu____8921 =
                let uu____8922 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8923 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8922 uu____8923
                 in
              failwith uu____8921
          | (uu____8924,FStar_Syntax_Syntax.U_bvar uu____8925) ->
              let uu____8926 =
                let uu____8927 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8928 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8927 uu____8928
                 in
              failwith uu____8926
          | (uu____8929,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8930 =
                let uu____8931 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8932 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8931 uu____8932
                 in
              failwith uu____8930
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8956 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8956
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8970 = occurs_univ v1 u3  in
              if uu____8970
              then
                let uu____8971 =
                  let uu____8972 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8973 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8972 uu____8973
                   in
                try_umax_components u11 u21 uu____8971
              else
                (let uu____8975 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8975)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8987 = occurs_univ v1 u3  in
              if uu____8987
              then
                let uu____8988 =
                  let uu____8989 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8990 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8989 uu____8990
                   in
                try_umax_components u11 u21 uu____8988
              else
                (let uu____8992 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8992)
          | (FStar_Syntax_Syntax.U_max uu____8993,uu____8994) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9000 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9000
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9002,FStar_Syntax_Syntax.U_max uu____9003) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9009 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9009
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9011,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9012,FStar_Syntax_Syntax.U_name
             uu____9013) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9014) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9015) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9016,FStar_Syntax_Syntax.U_succ
             uu____9017) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9018,FStar_Syntax_Syntax.U_zero
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
      let uu____9118 = bc1  in
      match uu____9118 with
      | (bs1,mk_cod1) ->
          let uu____9162 = bc2  in
          (match uu____9162 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9273 = aux xs ys  in
                     (match uu____9273 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9356 =
                       let uu____9363 = mk_cod1 xs  in ([], uu____9363)  in
                     let uu____9366 =
                       let uu____9373 = mk_cod2 ys  in ([], uu____9373)  in
                     (uu____9356, uu____9366)
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
                  let uu____9443 =
                    let uu____9444 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9444 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9443
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9449 = has_type_guard t1 t2  in (uu____9449, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9450 = has_type_guard t2 t1  in (uu____9450, wl)
  
let is_flex_pat :
  'Auu____9459 'Auu____9460 'Auu____9461 .
    ('Auu____9459,'Auu____9460,'Auu____9461 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___141_9474  ->
    match uu___141_9474 with
    | (uu____9483,uu____9484,[]) -> true
    | uu____9487 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9518 = f  in
      match uu____9518 with
      | (uu____9525,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9526;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9527;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9530;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9531;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9532;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9584  ->
                 match uu____9584 with
                 | (y,uu____9590) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9712 =
                  let uu____9725 =
                    let uu____9728 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9728  in
                  ((FStar_List.rev pat_binders), uu____9725)  in
                FStar_Pervasives_Native.Some uu____9712
            | (uu____9755,[]) ->
                let uu____9778 =
                  let uu____9791 =
                    let uu____9794 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9794  in
                  ((FStar_List.rev pat_binders), uu____9791)  in
                FStar_Pervasives_Native.Some uu____9778
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9859 =
                  let uu____9860 = FStar_Syntax_Subst.compress a  in
                  uu____9860.FStar_Syntax_Syntax.n  in
                (match uu____9859 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9878 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9878
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___169_9899 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___169_9899.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___169_9899.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9903 =
                            let uu____9904 =
                              let uu____9911 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9911)  in
                            FStar_Syntax_Syntax.NT uu____9904  in
                          [uu____9903]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___170_9923 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_9923.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___170_9923.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9924 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9952 =
                  let uu____9965 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9965  in
                (match uu____9952 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10028 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10055 ->
               let uu____10056 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10056 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10332 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10332
       then
         let uu____10333 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10333
       else ());
      (let uu____10335 = next_prob probs  in
       match uu____10335 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___171_10362 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___171_10362.wl_deferred);
               ctr = (uu___171_10362.ctr);
               defer_ok = (uu___171_10362.defer_ok);
               smt_ok = (uu___171_10362.smt_ok);
               tcenv = (uu___171_10362.tcenv);
               wl_implicits = (uu___171_10362.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10370 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10370
                 then
                   let uu____10371 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10371
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
                           (let uu___172_10376 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___172_10376.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___172_10376.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___172_10376.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___172_10376.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___172_10376.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___172_10376.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___172_10376.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___172_10376.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___172_10376.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10398 ->
                let uu____10407 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10466  ->
                          match uu____10466 with
                          | (c,uu____10474,uu____10475) -> c < probs.ctr))
                   in
                (match uu____10407 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10516 =
                            let uu____10521 =
                              FStar_List.map
                                (fun uu____10536  ->
                                   match uu____10536 with
                                   | (uu____10547,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10521, (probs.wl_implicits))  in
                          Success uu____10516
                      | uu____10550 ->
                          let uu____10559 =
                            let uu___173_10560 = probs  in
                            let uu____10561 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10580  ->
                                      match uu____10580 with
                                      | (uu____10587,uu____10588,y) -> y))
                               in
                            {
                              attempting = uu____10561;
                              wl_deferred = rest;
                              ctr = (uu___173_10560.ctr);
                              defer_ok = (uu___173_10560.defer_ok);
                              smt_ok = (uu___173_10560.smt_ok);
                              tcenv = (uu___173_10560.tcenv);
                              wl_implicits = (uu___173_10560.wl_implicits)
                            }  in
                          solve env uu____10559))))

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
            let uu____10595 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10595 with
            | USolved wl1 ->
                let uu____10597 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10597
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
                  let uu____10649 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10649 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10652 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10664;
                  FStar_Syntax_Syntax.vars = uu____10665;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10668;
                  FStar_Syntax_Syntax.vars = uu____10669;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10681,uu____10682) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10689,FStar_Syntax_Syntax.Tm_uinst uu____10690) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10697 -> USolved wl

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
            ((let uu____10707 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10707
              then
                let uu____10708 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10708 msg
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
               let uu____10794 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10794 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
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
                                                          (a2,uu____11244))
                                                           ->
                                                           let uu____11269 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11269
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11128
                                                uu____11150
                                               in
                                            match uu____11121 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___174_11295 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___174_11295.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___174_11295.tcenv);
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
                                                        ((let uu___175_11318
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___175_11318.attempting);
                                                            wl_deferred =
                                                              (uu___175_11318.wl_deferred);
                                                            ctr =
                                                              (uu___175_11318.ctr);
                                                            defer_ok =
                                                              (uu___175_11318.defer_ok);
                                                            smt_ok =
                                                              (uu___175_11318.smt_ok);
                                                            tcenv =
                                                              (uu___175_11318.tcenv);
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
                                             let uu____11516 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11516
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
                                         FStar_Syntax_Print.term_to_string
                                           t12
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
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
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
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
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
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12058 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___176_12061 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___176_12061.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___176_12061.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___176_12061.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___176_12061.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___176_12061.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___176_12061.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___176_12061.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___176_12061.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___176_12061.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12058)
                | uu____12062 ->
                    ((let uu____12064 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12064
                      then
                        let uu____12065 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12065
                      else ());
                     (let uu____12067 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12067 with
                      | (u,_args) ->
                          let uu____12104 =
                            let uu____12105 = FStar_Syntax_Subst.compress u
                               in
                            uu____12105.FStar_Syntax_Syntax.n  in
                          (match uu____12104 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12136 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12136 with
                                 | (u',uu____12152) ->
                                     let uu____12173 =
                                       let uu____12174 = whnf env u'  in
                                       uu____12174.FStar_Syntax_Syntax.n  in
                                     (match uu____12173 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12199 -> false)
                                  in
                               let uu____12200 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___142_12223  ->
                                         match uu___142_12223 with
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
                                              | uu____12232 -> false)
                                         | uu____12235 -> false))
                                  in
                               (match uu____12200 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12249 = whnf env this_rigid
                                         in
                                      let uu____12250 =
                                        FStar_List.collect
                                          (fun uu___143_12256  ->
                                             match uu___143_12256 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12262 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12262]
                                             | uu____12264 -> [])
                                          bounds_probs
                                         in
                                      uu____12249 :: uu____12250  in
                                    let uu____12265 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12265 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12296 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12311 =
                                               let uu____12312 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12312.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12311 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12324 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12324)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12333 -> bound  in
                                           let uu____12334 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12334)  in
                                         (match uu____12296 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12363 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12363
                                                then
                                                  let wl'1 =
                                                    let uu___177_12365 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
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
                                                  let uu____12366 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12366
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12369 =
                                                  solve_t env eq_prob
                                                    (let uu___178_12371 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___178_12371.wl_deferred);
                                                       ctr =
                                                         (uu___178_12371.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___178_12371.smt_ok);
                                                       tcenv =
                                                         (uu___178_12371.tcenv);
                                                       wl_implicits =
                                                         (uu___178_12371.wl_implicits)
                                                     })
                                                   in
                                                match uu____12369 with
                                                | Success uu____12372 ->
                                                    let wl2 =
                                                      let uu___179_12378 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___179_12378.wl_deferred);
                                                        ctr =
                                                          (uu___179_12378.ctr);
                                                        defer_ok =
                                                          (uu___179_12378.defer_ok);
                                                        smt_ok =
                                                          (uu___179_12378.smt_ok);
                                                        tcenv =
                                                          (uu___179_12378.tcenv);
                                                        wl_implicits =
                                                          (uu___179_12378.wl_implicits)
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
                                                    let uu____12393 =
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
                                                     (let uu____12405 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12405
                                                      then
                                                        let uu____12406 =
                                                          let uu____12407 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12407
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12406
                                                      else ());
                                                     (let uu____12413 =
                                                        let uu____12428 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12428)
                                                         in
                                                      match uu____12413 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12450))
                                                          ->
                                                          let uu____12475 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12475
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
                                                                 let uu____12492
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12492)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          let uu____12516 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12516
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
                                                                   let uu____12534
                                                                    =
                                                                    let uu____12539
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12539
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12534
                                                                    [] wl2
                                                                    in
                                                                 let uu____12544
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12544)))
                                                      | uu____12545 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12560 when flip ->
                               let uu____12561 =
                                 let uu____12562 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12563 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12562 uu____12563
                                  in
                               failwith uu____12561
                           | uu____12564 ->
                               let uu____12565 =
                                 let uu____12566 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12567 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12566 uu____12567
                                  in
                               failwith uu____12565)))))

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
                      (fun uu____12595  ->
                         match uu____12595 with
                         | (x,i) ->
                             let uu____12606 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12606, i)) bs_lhs
                     in
                  let uu____12607 = lhs  in
                  match uu____12607 with
                  | (uu____12608,u_lhs,uu____12610) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12723 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12733 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12733, univ)
                             in
                          match uu____12723 with
                          | (k,univ) ->
                              let uu____12742 =
                                let uu____12749 =
                                  let uu____12752 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12752
                                   in
                                copy_uvar u_lhs uu____12749 wl2  in
                              (match uu____12742 with
                               | (uu____12765,u,wl3) ->
                                   let uu____12768 =
                                     let uu____12771 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12771
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12768, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12807 =
                              let uu____12820 =
                                let uu____12829 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12829 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12875  ->
                                   fun uu____12876  ->
                                     match (uu____12875, uu____12876) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12967 =
                                           let uu____12974 =
                                             let uu____12977 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12977
                                              in
                                           copy_uvar u_lhs uu____12974 wl2
                                            in
                                         (match uu____12967 with
                                          | (uu____13000,t_a,wl3) ->
                                              let uu____13003 =
                                                let uu____13010 =
                                                  let uu____13013 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____13013
                                                   in
                                                copy_uvar u_lhs uu____13010
                                                  wl3
                                                 in
                                              (match uu____13003 with
                                               | (uu____13028,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12820
                                ([], wl1)
                               in
                            (match uu____12807 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___180_13089 = ct  in
                                   let uu____13090 =
                                     let uu____13093 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13093
                                      in
                                   let uu____13108 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___180_13089.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___180_13089.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13090;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13108;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___180_13089.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___181_13126 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___181_13126.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___181_13126.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13129 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13129 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13183 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13183 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13200 =
                                          let uu____13205 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13205)  in
                                        TERM uu____13200  in
                                      let uu____13206 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13206 with
                                       | (sub_prob,wl3) ->
                                           let uu____13217 =
                                             let uu____13218 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13218
                                              in
                                           solve env uu____13217))
                             | (x,imp)::formals2 ->
                                 let uu____13232 =
                                   let uu____13239 =
                                     let uu____13242 =
                                       let uu____13245 =
                                         let uu____13246 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13246
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13245
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13242
                                      in
                                   copy_uvar u_lhs uu____13239 wl1  in
                                 (match uu____13232 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13270 =
                                          let uu____13273 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13273
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13270 t_y
                                         in
                                      let uu____13274 =
                                        let uu____13277 =
                                          let uu____13280 =
                                            let uu____13281 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13281, imp)  in
                                          [uu____13280]  in
                                        FStar_List.append bs_terms
                                          uu____13277
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13274 formals2 wl2)
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
              (let uu____13323 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13323
               then
                 let uu____13324 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13325 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13324 (rel_to_string (p_rel orig)) uu____13325
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13430 = rhs wl1 scope env1 subst1  in
                     (match uu____13430 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13450 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13450
                            then
                              let uu____13451 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13451
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___182_13505 = hd1  in
                       let uu____13506 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_13505.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_13505.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13506
                       }  in
                     let hd21 =
                       let uu___183_13510 = hd2  in
                       let uu____13511 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___183_13510.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___183_13510.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13511
                       }  in
                     let uu____13514 =
                       let uu____13519 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13519
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13514 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13538 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13538
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13542 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13542 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13597 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13597
                                  in
                               ((let uu____13609 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13609
                                 then
                                   let uu____13610 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13611 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13610
                                     uu____13611
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13638 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13667 = aux wl [] env [] bs1 bs2  in
               match uu____13667 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13714 = attempt sub_probs wl2  in
                   solve env uu____13714)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13719 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13719 wl)

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
              let uu____13733 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13733 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13763 = lhs1  in
              match uu____13763 with
              | (uu____13766,ctx_u,uu____13768) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13774 ->
                        let uu____13775 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13775 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13822 = quasi_pattern env1 lhs1  in
              match uu____13822 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13852) ->
                  let uu____13857 = lhs1  in
                  (match uu____13857 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13871 = occurs_check ctx_u rhs1  in
                       (match uu____13871 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13913 =
                                let uu____13920 =
                                  let uu____13921 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13921
                                   in
                                FStar_Util.Inl uu____13920  in
                              (uu____13913, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13941 =
                                 let uu____13942 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13942  in
                               if uu____13941
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13962 =
                                    let uu____13969 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13969  in
                                  let uu____13974 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13962, uu____13974)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14036  ->
                     match uu____14036 with
                     | (x,i) ->
                         let uu____14047 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14047, i)) bs_lhs
                 in
              let uu____14048 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14048 with
              | (rhs_hd,args) ->
                  let uu____14085 = FStar_Util.prefix args  in
                  (match uu____14085 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14143 = lhs1  in
                       (match uu____14143 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14147 =
                              let uu____14158 =
                                let uu____14165 =
                                  let uu____14168 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14168
                                   in
                                copy_uvar u_lhs uu____14165 wl1  in
                              match uu____14158 with
                              | (uu____14189,t_last_arg,wl2) ->
                                  let uu____14192 =
                                    let uu____14199 =
                                      let uu____14202 =
                                        let uu____14209 =
                                          let uu____14216 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14216]  in
                                        FStar_List.append bs_lhs uu____14209
                                         in
                                      let uu____14233 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14202
                                        uu____14233
                                       in
                                    copy_uvar u_lhs uu____14199 wl2  in
                                  (match uu____14192 with
                                   | (uu____14246,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14252 =
                                         let uu____14259 =
                                           let uu____14262 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14262
                                            in
                                         copy_uvar u_lhs uu____14259 wl3  in
                                       (match uu____14252 with
                                        | (uu____14275,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14147 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14299 =
                                     let uu____14300 =
                                       let uu____14305 =
                                         let uu____14306 =
                                           let uu____14309 =
                                             let uu____14314 =
                                               let uu____14315 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14315]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14314
                                              in
                                           uu____14309
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14306
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14305)  in
                                     TERM uu____14300  in
                                   [uu____14299]  in
                                 let uu____14336 =
                                   let uu____14343 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14343 with
                                   | (p1,wl3) ->
                                       let uu____14360 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14360 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14336 with
                                  | (sub_probs,wl3) ->
                                      let uu____14387 =
                                        let uu____14388 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14388  in
                                      solve env1 uu____14387))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14421 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14421 with
                | (uu____14436,args) ->
                    (match args with | [] -> false | uu____14464 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14479 =
                  let uu____14480 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14480.FStar_Syntax_Syntax.n  in
                match uu____14479 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14483 -> true
                | uu____14496 -> false  in
              let uu____14497 = quasi_pattern env1 lhs1  in
              match uu____14497 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14508 =
                    let uu____14509 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14509
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14508
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14516 = is_app rhs1  in
                  if uu____14516
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14518 = is_arrow rhs1  in
                     if uu____14518
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14520 =
                          let uu____14521 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14521
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14520))
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
                let uu____14524 = lhs  in
                (match uu____14524 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14528 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14528 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14543 =
                              let uu____14546 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14546
                               in
                            FStar_All.pipe_right uu____14543
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14561 = occurs_check ctx_uv rhs1  in
                          (match uu____14561 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14583 =
                                   let uu____14584 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14584
                                    in
                                 giveup_or_defer env orig wl uu____14583
                               else
                                 (let uu____14586 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14586
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14591 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14591
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14593 =
                                         let uu____14594 =
                                           names_to_string1 fvs2  in
                                         let uu____14595 =
                                           names_to_string1 fvs1  in
                                         let uu____14596 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14594 uu____14595
                                           uu____14596
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14593)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14602 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14606 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14606 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14629 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14629
                             | (FStar_Util.Inl msg,uu____14631) ->
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
                  (let uu____14660 =
                     let uu____14677 = quasi_pattern env lhs  in
                     let uu____14684 = quasi_pattern env rhs  in
                     (uu____14677, uu____14684)  in
                   match uu____14660 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14727 = lhs  in
                       (match uu____14727 with
                        | ({ FStar_Syntax_Syntax.n = uu____14728;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14730;_},u_lhs,uu____14732)
                            ->
                            let uu____14735 = rhs  in
                            (match uu____14735 with
                             | (uu____14736,u_rhs,uu____14738) ->
                                 let uu____14739 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14739
                                 then
                                   let uu____14740 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14740
                                 else
                                   (let uu____14742 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14742 with
                                    | (sub_prob,wl1) ->
                                        let uu____14753 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14753 with
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
                                             let uu____14781 =
                                               let uu____14788 =
                                                 let uu____14791 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14791
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
                                                 uu____14788
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14781 with
                                              | (uu____14794,w,wl2) ->
                                                  let w_app =
                                                    let uu____14800 =
                                                      let uu____14805 =
                                                        FStar_List.map
                                                          (fun uu____14814 
                                                             ->
                                                             match uu____14814
                                                             with
                                                             | (z,uu____14820)
                                                                 ->
                                                                 let uu____14821
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14821)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14805
                                                       in
                                                    uu____14800
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14825 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14825
                                                    then
                                                      let uu____14826 =
                                                        let uu____14829 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14830 =
                                                          let uu____14833 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14834 =
                                                            let uu____14837 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14838 =
                                                              let uu____14841
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14846
                                                                =
                                                                let uu____14849
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14854
                                                                  =
                                                                  let uu____14857
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14857]
                                                                   in
                                                                uu____14849
                                                                  ::
                                                                  uu____14854
                                                                 in
                                                              uu____14841 ::
                                                                uu____14846
                                                               in
                                                            uu____14837 ::
                                                              uu____14838
                                                             in
                                                          uu____14833 ::
                                                            uu____14834
                                                           in
                                                        uu____14829 ::
                                                          uu____14830
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14826
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14863 =
                                                          let uu____14868 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14868)
                                                           in
                                                        TERM uu____14863  in
                                                      let uu____14869 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14869
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14874 =
                                                             let uu____14879
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
                                                               uu____14879)
                                                              in
                                                           TERM uu____14874
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14880 =
                                                      let uu____14881 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14881
                                                       in
                                                    solve env uu____14880)))))))
                   | uu____14882 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14946 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14946
            then
              let uu____14947 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14948 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14949 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14950 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14947 uu____14948 uu____14949 uu____14950
            else ());
           (let uu____14954 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14954
            then
              let uu____14955 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14956 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14957 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14958 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14955 uu____14956 uu____14957 uu____14958
            else ());
           (let uu____14960 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14960 with
            | (head1,args1) ->
                let uu____14997 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14997 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15051 =
                         let uu____15052 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15053 = args_to_string args1  in
                         let uu____15054 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15055 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15052 uu____15053 uu____15054 uu____15055
                          in
                       giveup env1 uu____15051 orig
                     else
                       (let uu____15057 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15063 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15063 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15057
                        then
                          let uu____15064 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15064 with
                          | USolved wl2 ->
                              let uu____15066 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15066
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15070 = base_and_refinement env1 t1  in
                           match uu____15070 with
                           | (base1,refinement1) ->
                               let uu____15095 = base_and_refinement env1 t2
                                  in
                               (match uu____15095 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15152 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15152 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15156 =
                                                FStar_List.fold_right2
                                                  (fun uu____15189  ->
                                                     fun uu____15190  ->
                                                       fun uu____15191  ->
                                                         match (uu____15189,
                                                                 uu____15190,
                                                                 uu____15191)
                                                         with
                                                         | ((a,uu____15227),
                                                            (a',uu____15229),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15250
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15250
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15156 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15278 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15278
                                                     then
                                                       let uu____15279 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15279
                                                     else ());
                                                    FStar_List.iter
                                                      (def_check_prob
                                                         "solve_t' subprobs")
                                                      subprobs;
                                                    (let formula =
                                                       let uu____15285 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15285
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     let uu____15293 =
                                                       attempt subprobs wl4
                                                        in
                                                     solve env1 uu____15293))))
                                     | uu____15294 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___184_15334 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___184_15334.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___184_15334.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___184_15334.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___184_15334.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___184_15334.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___184_15334.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___184_15334.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___184_15334.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15372 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15372
            then
              let uu____15373 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15374 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15375 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15376 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15373 uu____15374 uu____15375 uu____15376
            else ());
           (let uu____15378 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15378 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15409,uu____15410) ->
                     let rec may_relate head3 =
                       let uu____15437 =
                         let uu____15438 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15438.FStar_Syntax_Syntax.n  in
                       match uu____15437 with
                       | FStar_Syntax_Syntax.Tm_name uu____15441 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15442 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15465;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15466;
                             FStar_Syntax_Syntax.fv_qual = uu____15467;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15470;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15471;
                             FStar_Syntax_Syntax.fv_qual = uu____15472;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15476,uu____15477) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15519) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15525) ->
                           may_relate t
                       | uu____15530 -> false  in
                     let uu____15531 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15531
                     then
                       let uu____15532 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15532 with
                        | (guard,wl2) ->
                            let uu____15539 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15539)
                     else
                       (let uu____15541 =
                          let uu____15542 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15543 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15542 uu____15543
                           in
                        giveup env1 uu____15541 orig)
                 | (HeadMatch (true ),uu____15544) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15557 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15557 with
                        | (guard,wl2) ->
                            let uu____15564 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15564)
                     else
                       (let uu____15566 =
                          let uu____15567 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15568 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15567 uu____15568
                           in
                        giveup env1 uu____15566 orig)
                 | (uu____15569,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___185_15583 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___185_15583.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___185_15583.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___185_15583.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___185_15583.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___185_15583.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___185_15583.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___185_15583.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___185_15583.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15607 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15607
          then
            let uu____15608 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15608
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15613 =
                let uu____15616 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15616  in
              def_check_closed_in (p_loc orig) "ref.t1" uu____15613 t1);
             (let uu____15628 =
                let uu____15631 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15631  in
              def_check_closed_in (p_loc orig) "ref.t2" uu____15628 t2);
             (let uu____15643 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15643
              then
                let uu____15644 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15645 =
                  let uu____15646 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15647 =
                    let uu____15648 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15648  in
                  Prims.strcat uu____15646 uu____15647  in
                let uu____15649 =
                  let uu____15650 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15651 =
                    let uu____15652 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15652  in
                  Prims.strcat uu____15650 uu____15651  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15644
                  uu____15645 uu____15649
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15655,uu____15656) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15681,FStar_Syntax_Syntax.Tm_delayed uu____15682) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15707,uu____15708) ->
                  let uu____15735 =
                    let uu___186_15736 = problem  in
                    let uu____15737 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15736.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15737;
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15736.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___186_15736.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___186_15736.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15736.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15736.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15736.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15736.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15736.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15735 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15738,uu____15739) ->
                  let uu____15746 =
                    let uu___187_15747 = problem  in
                    let uu____15748 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15747.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15748;
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15747.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___187_15747.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___187_15747.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15747.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15747.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15747.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15747.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15747.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15746 wl
              | (uu____15749,FStar_Syntax_Syntax.Tm_ascribed uu____15750) ->
                  let uu____15777 =
                    let uu___188_15778 = problem  in
                    let uu____15779 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15778.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___188_15778.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15778.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15779;
                      FStar_TypeChecker_Common.element =
                        (uu___188_15778.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15778.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15778.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15778.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15778.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15778.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15777 wl
              | (uu____15780,FStar_Syntax_Syntax.Tm_meta uu____15781) ->
                  let uu____15788 =
                    let uu___189_15789 = problem  in
                    let uu____15790 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15789.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___189_15789.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15789.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15790;
                      FStar_TypeChecker_Common.element =
                        (uu___189_15789.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15789.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15789.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15789.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15789.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15789.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15788 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15792),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15794)) ->
                  let uu____15803 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15803
              | (FStar_Syntax_Syntax.Tm_bvar uu____15804,uu____15805) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15806,FStar_Syntax_Syntax.Tm_bvar uu____15807) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___144_15866 =
                    match uu___144_15866 with
                    | [] -> c
                    | bs ->
                        let uu____15888 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15888
                     in
                  let uu____15897 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15897 with
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
                                    let uu____16020 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____16020
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
                  let mk_t t l uu___145_16095 =
                    match uu___145_16095 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16129 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16129 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16248 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16249 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16248
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16249 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16250,uu____16251) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16278 -> true
                    | uu____16295 -> false  in
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
                      (let uu____16348 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16356 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16356.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16356.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16356.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16356.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16356.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16356.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16356.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16356.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16356.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16356.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16356.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16356.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16356.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16356.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16356.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16356.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16356.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16356.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16356.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16356.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16356.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16356.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16356.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16356.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16356.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16356.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16356.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16356.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16356.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16356.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16356.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16356.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16356.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16356.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16356.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16356.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16348 with
                       | (uu____16359,ty,uu____16361) ->
                           let uu____16362 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16362)
                     in
                  let uu____16363 =
                    let uu____16380 = maybe_eta t1  in
                    let uu____16387 = maybe_eta t2  in
                    (uu____16380, uu____16387)  in
                  (match uu____16363 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16429 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16429.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16429.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16429.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16429.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16429.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16429.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16429.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16429.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16450 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16450
                       then
                         let uu____16451 = destruct_flex_t not_abs wl  in
                         (match uu____16451 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16466 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16466.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16466.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16466.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16466.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16466.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16466.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16466.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16466.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16488 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16488
                       then
                         let uu____16489 = destruct_flex_t not_abs wl  in
                         (match uu____16489 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16504 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16504.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16504.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16504.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16504.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16504.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16504.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16504.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16504.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16506 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16523,FStar_Syntax_Syntax.Tm_abs uu____16524) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16551 -> true
                    | uu____16568 -> false  in
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
                      (let uu____16621 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16629 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16629.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16629.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16629.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16629.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16629.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16629.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16629.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16629.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16629.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16629.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16629.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16629.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16629.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16629.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16629.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16629.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16629.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16629.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16629.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16629.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16629.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16629.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16629.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16629.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16629.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16629.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16629.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16629.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16629.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16629.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16629.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16629.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16629.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16629.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16629.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16629.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16621 with
                       | (uu____16632,ty,uu____16634) ->
                           let uu____16635 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16635)
                     in
                  let uu____16636 =
                    let uu____16653 = maybe_eta t1  in
                    let uu____16660 = maybe_eta t2  in
                    (uu____16653, uu____16660)  in
                  (match uu____16636 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16702 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16702.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16702.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16702.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16702.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16702.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16702.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16702.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16702.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16723 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16723
                       then
                         let uu____16724 = destruct_flex_t not_abs wl  in
                         (match uu____16724 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16739 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16739.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16739.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16739.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16739.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16739.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16739.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16739.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16739.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16761 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16761
                       then
                         let uu____16762 = destruct_flex_t not_abs wl  in
                         (match uu____16762 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16777 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16777.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16777.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16777.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16777.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16777.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16777.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16777.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16777.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16779 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16811 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16811) &&
                       (let uu____16815 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16815))
                      &&
                      (let uu____16822 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16822 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___146_16834 =
                             match uu___146_16834 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16835 -> true
                             | uu____16836 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16837 -> false)
                     in
                  let uu____16838 = as_refinement should_delta env wl t1  in
                  (match uu____16838 with
                   | (x11,phi1) ->
                       let uu____16851 = as_refinement should_delta env wl t2
                          in
                       (match uu____16851 with
                        | (x21,phi21) ->
                            let uu____16864 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16864 with
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
                                   let uu____16930 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16930
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16942 =
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
                                   (let uu____16953 =
                                      let uu____16956 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16956
                                       in
                                    def_check_closed_in (p_loc orig) "ref.1"
                                      uu____16953 (p_guard base_prob));
                                   (let uu____16968 =
                                      let uu____16971 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16971
                                       in
                                    def_check_closed_in (p_loc orig) "ref.2"
                                      uu____16968 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____16983 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____16983)
                                    in
                                 let has_uvars =
                                   (let uu____16987 =
                                      let uu____16988 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16988  in
                                    Prims.op_Negation uu____16987) ||
                                     (let uu____16992 =
                                        let uu____16993 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16993
                                         in
                                      Prims.op_Negation uu____16992)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16996 =
                                     let uu____17001 =
                                       let uu____17002 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____17002]  in
                                     mk_t_problem wl1 uu____17001 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16996 with
                                    | (ref_prob,wl2) ->
                                        let uu____17017 =
                                          solve env1
                                            (let uu___193_17019 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___193_17019.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___193_17019.smt_ok);
                                               tcenv = (uu___193_17019.tcenv);
                                               wl_implicits =
                                                 (uu___193_17019.wl_implicits)
                                             })
                                           in
                                        (match uu____17017 with
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
                                         | Success uu____17029 ->
                                             let guard =
                                               let uu____17037 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____17037
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___194_17046 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___194_17046.attempting);
                                                 wl_deferred =
                                                   (uu___194_17046.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___194_17046.defer_ok);
                                                 smt_ok =
                                                   (uu___194_17046.smt_ok);
                                                 tcenv =
                                                   (uu___194_17046.tcenv);
                                                 wl_implicits =
                                                   (uu___194_17046.wl_implicits)
                                               }  in
                                             let uu____17047 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____17047))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17049,FStar_Syntax_Syntax.Tm_uvar uu____17050) ->
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
                    FStar_Syntax_Syntax.vars = uu____17095;_},uu____17096),FStar_Syntax_Syntax.Tm_uvar
                 uu____17097) ->
                  let uu____17146 = destruct_flex_t t1 wl  in
                  (match uu____17146 with
                   | (f1,wl1) ->
                       let uu____17153 = destruct_flex_t t2 wl1  in
                       (match uu____17153 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17160,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17161;
                    FStar_Syntax_Syntax.pos = uu____17162;
                    FStar_Syntax_Syntax.vars = uu____17163;_},uu____17164))
                  ->
                  let uu____17213 = destruct_flex_t t1 wl  in
                  (match uu____17213 with
                   | (f1,wl1) ->
                       let uu____17220 = destruct_flex_t t2 wl1  in
                       (match uu____17220 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17227;
                    FStar_Syntax_Syntax.pos = uu____17228;
                    FStar_Syntax_Syntax.vars = uu____17229;_},uu____17230),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17231;
                    FStar_Syntax_Syntax.pos = uu____17232;
                    FStar_Syntax_Syntax.vars = uu____17233;_},uu____17234))
                  ->
                  let uu____17303 = destruct_flex_t t1 wl  in
                  (match uu____17303 with
                   | (f1,wl1) ->
                       let uu____17310 = destruct_flex_t t2 wl1  in
                       (match uu____17310 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17317,uu____17318) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17333 = destruct_flex_t t1 wl  in
                  (match uu____17333 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17340;
                    FStar_Syntax_Syntax.pos = uu____17341;
                    FStar_Syntax_Syntax.vars = uu____17342;_},uu____17343),uu____17344)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17379 = destruct_flex_t t1 wl  in
                  (match uu____17379 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17386,FStar_Syntax_Syntax.Tm_uvar uu____17387) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17402,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17403;
                    FStar_Syntax_Syntax.pos = uu____17404;
                    FStar_Syntax_Syntax.vars = uu____17405;_},uu____17406))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17441,FStar_Syntax_Syntax.Tm_arrow uu____17442) ->
                  solve_t' env
                    (let uu___195_17470 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17470.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17470.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17470.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17470.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17470.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17470.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17470.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17470.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17470.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17471;
                    FStar_Syntax_Syntax.pos = uu____17472;
                    FStar_Syntax_Syntax.vars = uu____17473;_},uu____17474),FStar_Syntax_Syntax.Tm_arrow
                 uu____17475) ->
                  solve_t' env
                    (let uu___195_17523 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17523.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17523.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17523.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17523.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17523.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17523.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17523.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17523.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17523.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17524,FStar_Syntax_Syntax.Tm_uvar uu____17525) ->
                  let uu____17540 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17540
              | (uu____17541,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17542;
                    FStar_Syntax_Syntax.pos = uu____17543;
                    FStar_Syntax_Syntax.vars = uu____17544;_},uu____17545))
                  ->
                  let uu____17580 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17580
              | (FStar_Syntax_Syntax.Tm_uvar uu____17581,uu____17582) ->
                  let uu____17597 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17597
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17598;
                    FStar_Syntax_Syntax.pos = uu____17599;
                    FStar_Syntax_Syntax.vars = uu____17600;_},uu____17601),uu____17602)
                  ->
                  let uu____17637 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17637
              | (FStar_Syntax_Syntax.Tm_refine uu____17638,uu____17639) ->
                  let t21 =
                    let uu____17647 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17647  in
                  solve_t env
                    (let uu___196_17673 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___196_17673.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___196_17673.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___196_17673.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___196_17673.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___196_17673.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___196_17673.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___196_17673.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___196_17673.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___196_17673.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17674,FStar_Syntax_Syntax.Tm_refine uu____17675) ->
                  let t11 =
                    let uu____17683 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17683  in
                  solve_t env
                    (let uu___197_17709 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_17709.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_17709.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_17709.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_17709.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_17709.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___197_17709.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_17709.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_17709.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_17709.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17791 =
                    let uu____17792 = guard_of_prob env wl problem t1 t2  in
                    match uu____17792 with
                    | (guard,wl1) ->
                        let uu____17799 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17799
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____18010 = br1  in
                        (match uu____18010 with
                         | (p1,w1,uu____18035) ->
                             let uu____18052 = br2  in
                             (match uu____18052 with
                              | (p2,w2,uu____18071) ->
                                  let uu____18076 =
                                    let uu____18077 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____18077  in
                                  if uu____18076
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____18093 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____18093 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18126 = br2  in
                                         (match uu____18126 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18155 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18155
                                                 in
                                              let uu____18160 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18183,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18200) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18243 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18243 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18160
                                                (fun uu____18285  ->
                                                   match uu____18285 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18306 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18306
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18321 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18321
                                                              (fun
                                                                 uu____18345 
                                                                 ->
                                                                 match uu____18345
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18430 -> FStar_Pervasives_Native.None  in
                  let uu____18467 = solve_branches wl brs1 brs2  in
                  (match uu____18467 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18495 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18495 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18512 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18512  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18521 =
                              let uu____18522 =
                                attempt sub_probs1
                                  (let uu___198_18524 = wl3  in
                                   {
                                     attempting = (uu___198_18524.attempting);
                                     wl_deferred =
                                       (uu___198_18524.wl_deferred);
                                     ctr = (uu___198_18524.ctr);
                                     defer_ok = (uu___198_18524.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___198_18524.tcenv);
                                     wl_implicits =
                                       (uu___198_18524.wl_implicits)
                                   })
                                 in
                              solve env uu____18522  in
                            (match uu____18521 with
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
                       let uu____20530 = attempt sub_probs wl3  in
                       solve env uu____20530)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20553 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20556)::[] -> wp1
              | uu____20573 ->
                  let uu____20582 =
                    let uu____20583 =
                      let uu____20584 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20584  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20583
                     in
                  failwith uu____20582
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20590 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20590]
              | x -> x  in
            let uu____20592 =
              let uu____20601 =
                let uu____20608 =
                  let uu____20609 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20609 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20608  in
              [uu____20601]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20592;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20622 = lift_c1 ()  in solve_eq uu____20622 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___147_20628  ->
                       match uu___147_20628 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20629 -> false))
                in
             let uu____20630 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20656)::uu____20657,(wp2,uu____20659)::uu____20660)
                   -> (wp1, wp2)
               | uu____20713 ->
                   let uu____20734 =
                     let uu____20739 =
                       let uu____20740 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20741 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20740 uu____20741
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20739)
                      in
                   FStar_Errors.raise_error uu____20734
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20630 with
             | (wpc1,wpc2) ->
                 let uu____20748 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20748
                 then
                   let uu____20751 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20751 wl
                 else
                   (let uu____20753 =
                      let uu____20760 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20760  in
                    match uu____20753 with
                    | (c2_decl,qualifiers) ->
                        let uu____20781 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20781
                        then
                          let c1_repr =
                            let uu____20785 =
                              let uu____20786 =
                                let uu____20787 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20787  in
                              let uu____20788 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20786 uu____20788
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20785
                             in
                          let c2_repr =
                            let uu____20790 =
                              let uu____20791 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20792 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20791 uu____20792
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20790
                             in
                          let uu____20793 =
                            let uu____20798 =
                              let uu____20799 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20800 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20799 uu____20800
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20798
                             in
                          (match uu____20793 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____20804 = attempt [prob] wl2  in
                               solve env uu____20804)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20815 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20815
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20818 =
                                     let uu____20825 =
                                       let uu____20826 =
                                         let uu____20841 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20844 =
                                           let uu____20853 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
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
                                         (uu____20841, uu____20844)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20826
                                        in
                                     FStar_Syntax_Syntax.mk uu____20825  in
                                   uu____20818 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20917 =
                                    let uu____20924 =
                                      let uu____20925 =
                                        let uu____20940 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20943 =
                                          let uu____20952 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20959 =
                                            let uu____20968 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20975 =
                                              let uu____20984 =
                                                let uu____20991 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20991
                                                 in
                                              [uu____20984]  in
                                            uu____20968 :: uu____20975  in
                                          uu____20952 :: uu____20959  in
                                        (uu____20940, uu____20943)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20925
                                       in
                                    FStar_Syntax_Syntax.mk uu____20924  in
                                  uu____20917 FStar_Pervasives_Native.None r)
                              in
                           let uu____21035 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____21035 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____21043 =
                                   let uu____21046 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____21046
                                    in
                                 solve_prob orig uu____21043 [] wl1  in
                               let uu____21049 = attempt [base_prob] wl2  in
                               solve env uu____21049)))
           in
        let uu____21050 = FStar_Util.physical_equality c1 c2  in
        if uu____21050
        then
          let uu____21051 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21051
        else
          ((let uu____21054 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21054
            then
              let uu____21055 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21056 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21055
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21056
            else ());
           (let uu____21058 =
              let uu____21067 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21070 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21067, uu____21070)  in
            match uu____21058 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21088),FStar_Syntax_Syntax.Total
                    (t2,uu____21090)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21107 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21107 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21108,FStar_Syntax_Syntax.Total uu____21109) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21127),FStar_Syntax_Syntax.Total
                    (t2,uu____21129)) ->
                     let uu____21146 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21146 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21148),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21150)) ->
                     let uu____21167 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21167 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21169),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21171)) ->
                     let uu____21188 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21188 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21189,FStar_Syntax_Syntax.Comp uu____21190) ->
                     let uu____21199 =
                       let uu___199_21202 = problem  in
                       let uu____21205 =
                         let uu____21206 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21206
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21202.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21205;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21202.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21202.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21202.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21202.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21202.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21202.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21202.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21202.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21199 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21207,FStar_Syntax_Syntax.Comp uu____21208) ->
                     let uu____21217 =
                       let uu___199_21220 = problem  in
                       let uu____21223 =
                         let uu____21224 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21224
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21220.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21223;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21220.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21220.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21220.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21220.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21220.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21220.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21220.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21220.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21217 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21225,FStar_Syntax_Syntax.GTotal uu____21226) ->
                     let uu____21235 =
                       let uu___200_21238 = problem  in
                       let uu____21241 =
                         let uu____21242 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21242
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21238.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21238.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21238.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21241;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21238.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21238.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21238.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21238.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21238.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21238.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21235 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21243,FStar_Syntax_Syntax.Total uu____21244) ->
                     let uu____21253 =
                       let uu___200_21256 = problem  in
                       let uu____21259 =
                         let uu____21260 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21260
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21256.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21256.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21256.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21259;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21256.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21256.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21256.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21256.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21256.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21256.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21253 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21261,FStar_Syntax_Syntax.Comp uu____21262) ->
                     let uu____21263 =
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
                     if uu____21263
                     then
                       let uu____21264 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21264 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21268 =
                            let uu____21273 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21273
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21279 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21280 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21279, uu____21280))
                             in
                          match uu____21268 with
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
                           (let uu____21287 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21287
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21289 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21289 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21292 =
                                  let uu____21293 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21294 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21293 uu____21294
                                   in
                                giveup env uu____21292 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21301 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21329  ->
              match uu____21329 with
              | (uu____21338,tm,uu____21340,uu____21341) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21301 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21374 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21374 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21392 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21420  ->
                match uu____21420 with
                | (u1,u2) ->
                    let uu____21427 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21428 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21427 uu____21428))
         in
      FStar_All.pipe_right uu____21392 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21455,[])) -> "{}"
      | uu____21480 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21503 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21503
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21506 =
              FStar_List.map
                (fun uu____21516  ->
                   match uu____21516 with
                   | (uu____21521,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21506 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21526 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21526 imps
  
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
                  let uu____21579 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21579
                  then
                    let uu____21580 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21581 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21580
                      (rel_to_string rel) uu____21581
                  else "TOP"  in
                let uu____21583 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21583 with
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
              let uu____21641 =
                let uu____21644 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21644
                 in
              FStar_Syntax_Syntax.new_bv uu____21641 t1  in
            let uu____21647 =
              let uu____21652 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21652
               in
            match uu____21647 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21725 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21725
              then
                let uu____21726 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21726
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
          ((let uu____21748 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21748
            then
              let uu____21749 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21749
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21753 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21753
             then
               let uu____21754 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21754
             else ());
            (let f2 =
               let uu____21757 =
                 let uu____21758 = FStar_Syntax_Util.unmeta f1  in
                 uu____21758.FStar_Syntax_Syntax.n  in
               match uu____21757 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21762 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___201_21763 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___201_21763.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___201_21763.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___201_21763.FStar_TypeChecker_Env.implicits)
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
            let uu____21865 =
              let uu____21866 =
                let uu____21867 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21867;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21866  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21865
  
let with_guard_no_simp :
  'Auu____21882 .
    'Auu____21882 ->
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
            let uu____21905 =
              let uu____21906 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21906;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21905
  
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
          (let uu____21944 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21944
           then
             let uu____21945 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21946 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21945
               uu____21946
           else ());
          (let uu____21948 =
             let uu____21953 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21953
              in
           match uu____21948 with
           | (prob,wl) ->
               let g =
                 let uu____21961 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21979  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21961  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22021 = try_teq true env t1 t2  in
        match uu____22021 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22025 = FStar_TypeChecker_Env.get_range env  in
              let uu____22026 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22025 uu____22026);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22033 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22033
              then
                let uu____22034 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22035 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22036 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22034
                  uu____22035 uu____22036
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
          let uu____22058 = FStar_TypeChecker_Env.get_range env  in
          let uu____22059 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22058 uu____22059
  
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
        (let uu____22084 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22084
         then
           let uu____22085 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22086 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____22085 uu____22086
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____22089 =
           let uu____22096 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____22096 "sub_comp"
            in
         match uu____22089 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____22107 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____22125  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____22107)))
  
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
      fun uu____22178  ->
        match uu____22178 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22221 =
                 let uu____22226 =
                   let uu____22227 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22228 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22227 uu____22228
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22226)  in
               let uu____22229 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22221 uu____22229)
               in
            let equiv1 v1 v' =
              let uu____22241 =
                let uu____22246 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22247 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22246, uu____22247)  in
              match uu____22241 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22266 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22296 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22296 with
                      | FStar_Syntax_Syntax.U_unif uu____22303 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22332  ->
                                    match uu____22332 with
                                    | (u,v') ->
                                        let uu____22341 = equiv1 v1 v'  in
                                        if uu____22341
                                        then
                                          let uu____22344 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22344 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22360 -> []))
               in
            let uu____22365 =
              let wl =
                let uu___202_22369 = empty_worklist env  in
                {
                  attempting = (uu___202_22369.attempting);
                  wl_deferred = (uu___202_22369.wl_deferred);
                  ctr = (uu___202_22369.ctr);
                  defer_ok = false;
                  smt_ok = (uu___202_22369.smt_ok);
                  tcenv = (uu___202_22369.tcenv);
                  wl_implicits = (uu___202_22369.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22387  ->
                      match uu____22387 with
                      | (lb,v1) ->
                          let uu____22394 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22394 with
                           | USolved wl1 -> ()
                           | uu____22396 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22406 =
              match uu____22406 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22415) -> true
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
                      uu____22438,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22440,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22451) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22458,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22466 -> false)
               in
            let uu____22471 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22486  ->
                      match uu____22486 with
                      | (u,v1) ->
                          let uu____22493 = check_ineq (u, v1)  in
                          if uu____22493
                          then true
                          else
                            ((let uu____22496 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22496
                              then
                                let uu____22497 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22498 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22497
                                  uu____22498
                              else ());
                             false)))
               in
            if uu____22471
            then ()
            else
              ((let uu____22502 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22502
                then
                  ((let uu____22504 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22504);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22514 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22514))
                else ());
               (let uu____22524 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22524))
  
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
        let fail1 uu____22591 =
          match uu____22591 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___203_22612 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___203_22612.attempting);
            wl_deferred = (uu___203_22612.wl_deferred);
            ctr = (uu___203_22612.ctr);
            defer_ok;
            smt_ok = (uu___203_22612.smt_ok);
            tcenv = (uu___203_22612.tcenv);
            wl_implicits = (uu___203_22612.wl_implicits)
          }  in
        (let uu____22614 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22614
         then
           let uu____22615 = FStar_Util.string_of_bool defer_ok  in
           let uu____22616 = wl_to_string wl  in
           let uu____22617 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22615 uu____22616 uu____22617
         else ());
        (let g1 =
           let uu____22628 = solve_and_commit env wl fail1  in
           match uu____22628 with
           | FStar_Pervasives_Native.Some
               (uu____22635::uu____22636,uu____22637) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___204_22662 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___204_22662.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___204_22662.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22671 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___205_22679 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___205_22679.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___205_22679.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___205_22679.FStar_TypeChecker_Env.implicits)
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
    let uu____22727 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22727 with
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
            let uu___206_22850 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___206_22850.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___206_22850.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___206_22850.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22851 =
            let uu____22852 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22852  in
          if uu____22851
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22860 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22861 =
                       let uu____22862 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22862
                        in
                     FStar_Errors.diag uu____22860 uu____22861)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22866 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22867 =
                        let uu____22868 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22868
                         in
                      FStar_Errors.diag uu____22866 uu____22867)
                   else ();
                   (let uu____22871 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22871 "discharge_guard'"
                      env vc1);
                   (let uu____22872 = check_trivial vc1  in
                    match uu____22872 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22879 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22880 =
                                let uu____22881 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22881
                                 in
                              FStar_Errors.diag uu____22879 uu____22880)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22886 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22887 =
                                let uu____22888 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22888
                                 in
                              FStar_Errors.diag uu____22886 uu____22887)
                           else ();
                           (let vcs =
                              let uu____22901 = FStar_Options.use_tactics ()
                                 in
                              if uu____22901
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22923  ->
                                     (let uu____22925 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22925);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22968  ->
                                              match uu____22968 with
                                              | (env1,goal,opts) ->
                                                  let uu____22984 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22984, opts)))))
                              else
                                (let uu____22986 =
                                   let uu____22995 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22995)  in
                                 [uu____22986])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23038  ->
                                    match uu____23038 with
                                    | (env1,goal,opts) ->
                                        let uu____23054 = check_trivial goal
                                           in
                                        (match uu____23054 with
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
                                                (let uu____23062 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23063 =
                                                   let uu____23064 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____23065 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23064 uu____23065
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23062 uu____23063)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23068 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23069 =
                                                   let uu____23070 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23070
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23068 uu____23069)
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
      let uu____23084 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23084 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23091 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23091
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23102 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23102 with
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
            let uu____23135 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23135 with
            | FStar_Pervasives_Native.Some uu____23138 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23158 = acc  in
            match uu____23158 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23210 = hd1  in
                     (match uu____23210 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23224 = unresolved ctx_u  in
                             if uu____23224
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___207_23236 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___207_23236.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___207_23236.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___207_23236.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___207_23236.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___207_23236.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___207_23236.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___207_23236.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___207_23236.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___207_23236.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___207_23236.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___207_23236.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___207_23236.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___207_23236.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___207_23236.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___207_23236.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___207_23236.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___207_23236.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___207_23236.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___207_23236.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___207_23236.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___207_23236.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___207_23236.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___207_23236.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___207_23236.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___207_23236.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___207_23236.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___207_23236.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___207_23236.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___207_23236.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___207_23236.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___207_23236.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___207_23236.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___207_23236.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___207_23236.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___207_23236.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___207_23236.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___207_23236.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___207_23236.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___208_23239 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___208_23239.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___208_23239.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___208_23239.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___208_23239.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___208_23239.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___208_23239.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___208_23239.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___208_23239.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___208_23239.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___208_23239.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___208_23239.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___208_23239.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___208_23239.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___208_23239.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___208_23239.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___208_23239.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___208_23239.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___208_23239.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___208_23239.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___208_23239.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___208_23239.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___208_23239.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___208_23239.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___208_23239.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___208_23239.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___208_23239.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___208_23239.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___208_23239.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___208_23239.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___208_23239.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___208_23239.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___208_23239.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___208_23239.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23242 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23242
                                   then
                                     let uu____23243 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23244 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23245 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23246 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23243 uu____23244 uu____23245
                                       reason uu____23246
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23257 =
                                             let uu____23266 =
                                               let uu____23273 =
                                                 let uu____23274 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23275 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23276 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23274 uu____23275
                                                   uu____23276
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23273, r)
                                                in
                                             [uu____23266]  in
                                           FStar_Errors.add_errors
                                             uu____23257);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___211_23290 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___211_23290.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___211_23290.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___211_23290.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23293 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23303  ->
                                               let uu____23304 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23305 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23306 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23304 uu____23305
                                                 reason uu____23306)) env2 g2
                                         true
                                        in
                                     match uu____23293 with
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
          let uu___212_23316 = g  in
          let uu____23317 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___212_23316.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___212_23316.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___212_23316.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23317
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
        let uu____23367 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23367 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23376 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23376
      | (reason,e,ctx_u,r)::uu____23381 ->
          let uu____23400 =
            let uu____23405 =
              let uu____23406 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23407 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23406 uu____23407 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23405)
             in
          FStar_Errors.raise_error uu____23400 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___213_23418 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___213_23418.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___213_23418.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___213_23418.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23433 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23433 with
      | FStar_Pervasives_Native.Some uu____23439 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23455 = try_teq false env t1 t2  in
        match uu____23455 with
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
        (let uu____23489 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23489
         then
           let uu____23490 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23491 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23490
             uu____23491
         else ());
        (let uu____23493 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23493 with
         | (prob,x,wl) ->
             let g =
               let uu____23512 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23530  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23512  in
             ((let uu____23558 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23558
               then
                 let uu____23559 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23560 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23561 =
                   let uu____23562 = FStar_Util.must g  in
                   guard_to_string env uu____23562  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23559 uu____23560 uu____23561
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
        let uu____23596 = check_subtyping env t1 t2  in
        match uu____23596 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23615 =
              let uu____23616 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23616 g  in
            FStar_Pervasives_Native.Some uu____23615
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23634 = check_subtyping env t1 t2  in
        match uu____23634 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23653 =
              let uu____23654 =
                let uu____23655 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23655]  in
              close_guard env uu____23654 g  in
            FStar_Pervasives_Native.Some uu____23653
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23684 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23684
         then
           let uu____23685 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23686 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23685
             uu____23686
         else ());
        (let uu____23688 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23688 with
         | (prob,x,wl) ->
             let g =
               let uu____23701 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23719  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23701  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23748 =
                      let uu____23749 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23749]  in
                    close_guard env uu____23748 g1  in
                  discharge_guard_nosmt env g2))
  