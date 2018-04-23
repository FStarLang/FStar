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
        FStar_TypeChecker_Env.univ_ineqs = uu____39;
        FStar_TypeChecker_Env.implicits = uu____40;_} -> true
    | uu____65 -> false
  
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
          let uu___110_102 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___110_102.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___110_102.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___110_102.FStar_TypeChecker_Env.implicits)
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
          let uu____137 = FStar_Options.defensive ()  in
          if uu____137
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____141 =
              let uu____142 =
                let uu____143 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____143  in
              Prims.op_Negation uu____142  in
            (if uu____141
             then
               let uu____148 =
                 let uu____153 =
                   let uu____154 = FStar_Syntax_Print.term_to_string t  in
                   let uu____155 =
                     let uu____156 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____156
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____154 uu____155
                    in
                 (FStar_Errors.Warning_Defensive, uu____153)  in
               FStar_Errors.log_issue rng uu____148
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____178 =
          let uu____179 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____179  in
        if uu____178
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
          let uu____205 =
            let uu____206 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____206  in
          if uu____205
          then ()
          else
            (let uu____208 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____208 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____231 =
            let uu____232 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____232  in
          if uu____231
          then ()
          else
            (let uu____234 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____234 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___111_248 = g  in
          let uu____249 =
            let uu____250 =
              let uu____251 =
                let uu____258 =
                  let uu____259 =
                    let uu____274 =
                      let uu____283 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____283]  in
                    (f, uu____274)  in
                  FStar_Syntax_Syntax.Tm_app uu____259  in
                FStar_Syntax_Syntax.mk uu____258  in
              uu____251 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____250
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____249;
            FStar_TypeChecker_Env.deferred =
              (uu___111_248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___111_248.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___111_248.FStar_TypeChecker_Env.implicits)
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
          let uu___112_313 = g  in
          let uu____314 =
            let uu____315 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____315  in
          {
            FStar_TypeChecker_Env.guard_f = uu____314;
            FStar_TypeChecker_Env.deferred =
              (uu___112_313.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___112_313.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___112_313.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____321 -> failwith "impossible"
  
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
          let uu____336 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____336
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____342 =
      let uu____343 = FStar_Syntax_Util.unmeta t  in
      uu____343.FStar_Syntax_Syntax.n  in
    match uu____342 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____347 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____388 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____388;
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
                       let uu____467 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____467
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___113_469 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___113_469.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___113_469.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___113_469.FStar_TypeChecker_Env.implicits)
            }
  
let (close_forall :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____494 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____494
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
            let uu___114_513 = g  in
            let uu____514 =
              let uu____515 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____515  in
            {
              FStar_TypeChecker_Env.guard_f = uu____514;
              FStar_TypeChecker_Env.deferred =
                (uu___114_513.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___114_513.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___114_513.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____544 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____574 -> false
  
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
          FStar_Syntax_Syntax.binders ->
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
                  let uu____849 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____849;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                  should_check gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar ctx_uvar)
                     FStar_Pervasives_Native.None r
                    in
                 (ctx_uvar, t,
                   (let uu___115_865 = wl  in
                    {
                      attempting = (uu___115_865.attempting);
                      wl_deferred = (uu___115_865.wl_deferred);
                      ctr = (uu___115_865.ctr);
                      defer_ok = (uu___115_865.defer_ok);
                      smt_ok = (uu___115_865.smt_ok);
                      tcenv = (uu___115_865.tcenv);
                      wl_implicits = ((reason, t, ctx_uvar, r, should_check)
                        :: (wl.wl_implicits))
                    })))
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____906 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____936 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____961 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____967 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____973 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
[@@deriving show]
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
[@@deriving show]
type 'a problem_t = 'a FStar_TypeChecker_Common.problem[@@deriving show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___85_988  ->
    match uu___85_988 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____994 =
      let uu____995 = FStar_Syntax_Subst.compress t  in
      uu____995.FStar_Syntax_Syntax.n  in
    match uu____994 with
    | FStar_Syntax_Syntax.Tm_uvar u -> print_ctx_uvar u
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar u;
           FStar_Syntax_Syntax.pos = uu____1000;
           FStar_Syntax_Syntax.vars = uu____1001;_},args)
        ->
        let uu____1023 = print_ctx_uvar u  in
        let uu____1024 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____1023 uu____1024
    | uu____1025 -> FStar_Syntax_Print.term_to_string t
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___86_1035  ->
      match uu___86_1035 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1039 =
            let uu____1042 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1043 =
              let uu____1046 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1047 =
                let uu____1050 =
                  let uu____1053 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1053]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1050
                 in
              uu____1046 :: uu____1047  in
            uu____1042 :: uu____1043  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1039
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1057 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1058 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1059 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1057 uu____1058
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1059
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___87_1069  ->
      match uu___87_1069 with
      | UNIV (u,t) ->
          let x =
            let uu____1073 = FStar_Options.hide_uvar_nums ()  in
            if uu____1073
            then "?"
            else
              (let uu____1075 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1075 FStar_Util.string_of_int)
             in
          let uu____1076 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1076
      | TERM (u,t) ->
          let x =
            let uu____1080 = FStar_Options.hide_uvar_nums ()  in
            if uu____1080
            then "?"
            else
              (let uu____1082 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1082 FStar_Util.string_of_int)
             in
          let uu____1083 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1083
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1098 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1098 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1112 =
      let uu____1115 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1115
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1112 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1128 .
    (FStar_Syntax_Syntax.term,'Auu____1128) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1146 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1164  ->
              match uu____1164 with
              | (x,uu____1170) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1146 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1178 =
      let uu____1179 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1179  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1178;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___116_1211 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___116_1211.wl_deferred);
          ctr = (uu___116_1211.ctr);
          defer_ok = (uu___116_1211.defer_ok);
          smt_ok;
          tcenv = (uu___116_1211.tcenv);
          wl_implicits = (uu___116_1211.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1218 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1218,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___117_1241 = empty_worklist env  in
      let uu____1242 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1242;
        wl_deferred = (uu___117_1241.wl_deferred);
        ctr = (uu___117_1241.ctr);
        defer_ok = (uu___117_1241.defer_ok);
        smt_ok = (uu___117_1241.smt_ok);
        tcenv = (uu___117_1241.tcenv);
        wl_implicits = (uu___117_1241.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___118_1262 = wl  in
        {
          attempting = (uu___118_1262.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___118_1262.ctr);
          defer_ok = (uu___118_1262.defer_ok);
          smt_ok = (uu___118_1262.smt_ok);
          tcenv = (uu___118_1262.tcenv);
          wl_implicits = (uu___118_1262.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___119_1283 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___119_1283.wl_deferred);
        ctr = (uu___119_1283.ctr);
        defer_ok = (uu___119_1283.defer_ok);
        smt_ok = (uu___119_1283.smt_ok);
        tcenv = (uu___119_1283.tcenv);
        wl_implicits = (uu___119_1283.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1300 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1300
         then
           let uu____1301 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1301
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___88_1307  ->
    match uu___88_1307 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1312 .
    'Auu____1312 FStar_TypeChecker_Common.problem ->
      'Auu____1312 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___120_1324 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___120_1324.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___120_1324.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___120_1324.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___120_1324.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.scope =
        (uu___120_1324.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___120_1324.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___120_1324.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___120_1324.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1331 .
    'Auu____1331 FStar_TypeChecker_Common.problem ->
      'Auu____1331 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___89_1348  ->
    match uu___89_1348 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___90_1363  ->
    match uu___90_1363 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___121_1369 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___121_1369.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___121_1369.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___121_1369.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___121_1369.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___121_1369.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___121_1369.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.scope =
               (uu___121_1369.FStar_TypeChecker_Common.scope);
             FStar_TypeChecker_Common.reason =
               (uu___121_1369.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___121_1369.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___121_1369.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___122_1377 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___122_1377.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___122_1377.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___122_1377.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___122_1377.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___122_1377.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___122_1377.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.scope =
               (uu___122_1377.FStar_TypeChecker_Common.scope);
             FStar_TypeChecker_Common.reason =
               (uu___122_1377.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___122_1377.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___122_1377.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___91_1389  ->
      match uu___91_1389 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___92_1394  ->
    match uu___92_1394 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___93_1405  ->
    match uu___93_1405 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___94_1418  ->
    match uu___94_1418 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___95_1431  ->
    match uu___95_1431 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___96_1442  ->
    match uu___96_1442 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___97_1459  ->
    match uu___97_1459 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1480 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1480) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1508 =
          let uu____1509 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1509  in
        if uu____1508
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1543)::bs ->
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
      | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
      | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1602 =
          let uu____1603 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1603  in
        if uu____1602
        then ()
        else
          (let uu____1605 =
             let uu____1608 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1608
              in
           def_check_closed_in (p_loc prob) msg uu____1605 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1638 =
         let uu____1639 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1639  in
       if uu____1638
       then ()
       else
         (let uu____1641 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1641));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1653 -> ())
  
let (mk_eq2 :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1683 = FStar_Syntax_Util.type_u ()  in
          match uu____1683 with
          | (t_type,u) ->
              let uu____1694 =
                let uu____1701 = p_scope prob  in
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma uu____1701 t_type
                  false
                 in
              (match uu____1694 with
               | (uu____1706,tt,wl1) ->
                   let uu____1709 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1709, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___98_1714  ->
    match uu___98_1714 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1730 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1730 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1740  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1838 .
    worklist ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1838 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1838 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1838 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____1889 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma scope
                      FStar_Syntax_Util.ktype0 false
                     in
                  match uu____1889 with
                  | (ctx_uvar,lg,wl1) ->
                      let uu____1905 =
                        let uu____1908 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1908;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (FStar_Pervasives_Native.None, ctx_uvar);
                          FStar_TypeChecker_Common.scope = scope;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (uu____1905, wl1)
  
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
                  let uu____1961 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____1961 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.TProb p), wl1)
  
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
                  let uu____2026 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2026 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2061 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2061 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2061 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2061 FStar_TypeChecker_Common.problem,worklist)
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
                  let scope = FStar_TypeChecker_Env.all_binders env  in
                  let uu____2113 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2135 =
                          let uu____2138 =
                            let uu____2145 = FStar_Syntax_Syntax.mk_binder x
                               in
                            [uu____2145]  in
                          let uu____2158 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow uu____2138 uu____2158  in
                        let uu____2159 =
                          let uu____2162 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2162  in
                        (uu____2135, uu____2159)
                     in
                  match uu____2113 with
                  | (lg_ty,elt) ->
                      let uu____2183 =
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___123_2191 = wl  in
                           {
                             attempting = (uu___123_2191.attempting);
                             wl_deferred = (uu___123_2191.wl_deferred);
                             ctr = (uu___123_2191.ctr);
                             defer_ok = (uu___123_2191.defer_ok);
                             smt_ok = (uu___123_2191.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___123_2191.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma scope lg_ty
                          false
                         in
                      (match uu____2183 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2203 =
                                   let uu____2208 =
                                     let uu____2209 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2209]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2208
                                    in
                                 uu____2203 FStar_Pervasives_Native.None loc
                              in
                           let uu____2230 =
                             let uu____2233 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2233;
                               FStar_TypeChecker_Common.lhs = lhs;
                               FStar_TypeChecker_Common.relation = rel;
                               FStar_TypeChecker_Common.rhs = rhs;
                               FStar_TypeChecker_Common.element = elt;
                               FStar_TypeChecker_Common.logical_guard = lg1;
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (subject, ctx_uvar);
                               FStar_TypeChecker_Common.scope = scope;
                               FStar_TypeChecker_Common.reason = [reason];
                               FStar_TypeChecker_Common.loc = loc;
                               FStar_TypeChecker_Common.rank =
                                 FStar_Pervasives_Native.None
                             }  in
                           (uu____2230, wl1))
  
let problem_using_guard :
  'Auu____2252 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2252 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2252 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2252 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2289 = next_pid ()  in
              let uu____2290 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____2289;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.logical_guard_uvar =
                  (p_guard_uvar orig);
                FStar_TypeChecker_Common.scope = uu____2290;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____2301 .
    worklist ->
      'Auu____2301 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ
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
        let uu____2345 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____2345
        then
          let uu____2346 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2347 = prob_to_string env d  in
          let uu____2348 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2346 uu____2347 uu____2348 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2354 -> failwith "impossible"  in
           let uu____2355 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2367 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2368 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2367, uu____2368)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2372 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2373 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2372, uu____2373)
              in
           match uu____2355 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___99_2391  ->
            match uu___99_2391 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2403 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___100_2425  ->
           match uu___100_2425 with
           | UNIV uu____2428 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2435 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2435
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
        (fun uu___101_2459  ->
           match uu___101_2459 with
           | UNIV (u',t) ->
               let uu____2464 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2464
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2468 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2479 =
        let uu____2480 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2480
         in
      FStar_Syntax_Subst.compress uu____2479
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2491 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2491
  
let norm_arg :
  'Auu____2498 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2498) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2498)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2521 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2521, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2562  ->
              match uu____2562 with
              | (x,imp) ->
                  let uu____2573 =
                    let uu___124_2574 = x  in
                    let uu____2575 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___124_2574.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___124_2574.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2575
                    }  in
                  (uu____2573, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2596 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2596
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2600 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2600
        | uu____2603 -> u2  in
      let uu____2604 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2604
  
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
                FStar_Syntax_Syntax.Delta_constant]
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
                (let uu____2726 = norm_refinement env t12  in
                 match uu____2726 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2743;
                     FStar_Syntax_Syntax.vars = uu____2744;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2770 =
                       let uu____2771 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2772 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2771 uu____2772
                        in
                     failwith uu____2770)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2788 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2788
          | FStar_Syntax_Syntax.Tm_uinst uu____2789 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2826 =
                   let uu____2827 = FStar_Syntax_Subst.compress t1'  in
                   uu____2827.FStar_Syntax_Syntax.n  in
                 match uu____2826 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2844 -> aux true t1'
                 | uu____2851 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2866 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2897 =
                   let uu____2898 = FStar_Syntax_Subst.compress t1'  in
                   uu____2898.FStar_Syntax_Syntax.n  in
                 match uu____2897 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2915 -> aux true t1'
                 | uu____2922 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2937 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2982 =
                   let uu____2983 = FStar_Syntax_Subst.compress t1'  in
                   uu____2983.FStar_Syntax_Syntax.n  in
                 match uu____2982 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3000 -> aux true t1'
                 | uu____3007 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3022 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3037 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3052 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3067 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3082 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3109 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3140 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3161 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3176 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3203 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3240 ->
              let uu____3247 =
                let uu____3248 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3249 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3248 uu____3249
                 in
              failwith uu____3247
          | FStar_Syntax_Syntax.Tm_ascribed uu____3264 ->
              let uu____3291 =
                let uu____3292 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3293 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3292 uu____3293
                 in
              failwith uu____3291
          | FStar_Syntax_Syntax.Tm_delayed uu____3308 ->
              let uu____3333 =
                let uu____3334 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3335 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3334 uu____3335
                 in
              failwith uu____3333
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3350 =
                let uu____3351 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3352 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3351 uu____3352
                 in
              failwith uu____3350
           in
        let uu____3367 = whnf env t1  in aux false uu____3367
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3398 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3398 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3429 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3429 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3465 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3465, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3476 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3476 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3501 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3501 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                                      FStar_Syntax_Syntax.syntax)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____3584  ->
    match uu____3584 with
    | (t_base,refopt) ->
        let uu____3617 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3617 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3675 =
      let uu____3678 =
        let uu____3681 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3704  ->
                  match uu____3704 with | (uu____3711,uu____3712,x) -> x))
           in
        FStar_List.append wl.attempting uu____3681  in
      FStar_List.map (wl_prob_to_string wl) uu____3678  in
    FStar_All.pipe_right uu____3675 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3731 =
          let uu____3744 =
            let uu____3745 = FStar_Syntax_Subst.compress k  in
            uu____3745.FStar_Syntax_Syntax.n  in
          match uu____3744 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3798 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3798)
              else
                (let uu____3812 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3812 with
                 | (ys',t1,uu____3835) ->
                     let uu____3840 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3840))
          | uu____3881 ->
              let uu____3882 =
                let uu____3893 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3893)  in
              ((ys, t), uu____3882)
           in
        match uu____3731 with
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
                 let uu____3942 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3942 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
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
             let uu____3981 = p_guard_uvar prob  in
             match uu____3981 with
             | (xopt,uv) ->
                 ((let uu____3995 =
                     FStar_Syntax_Unionfind.find
                       uv.FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____3995 with
                   | FStar_Pervasives_Native.None  ->
                       ((let uu____3999 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3999
                         then
                           let uu____4000 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____4001 = print_ctx_uvar uv  in
                           let uu____4002 =
                             FStar_Syntax_Print.term_to_string phi  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____4000
                             uu____4001 uu____4002
                         else ());
                        (let phi1 =
                           match xopt with
                           | FStar_Pervasives_Native.None  -> phi
                           | FStar_Pervasives_Native.Some x ->
                               let uu____4006 =
                                 let uu____4007 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4007]  in
                               FStar_Syntax_Util.abs uu____4006 phi
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Util.residual_tot
                                       FStar_Syntax_Util.ktype0))
                            in
                         def_check_closed (p_loc prob) "solve_prob'" phi1;
                         FStar_Syntax_Util.set_uvar
                           uv.FStar_Syntax_Syntax.ctx_uvar_head phi1))
                   | FStar_Pervasives_Native.Some uu____4021 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___125_4024 = wl  in
                   {
                     attempting = (uu___125_4024.attempting);
                     wl_deferred = (uu___125_4024.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___125_4024.defer_ok);
                     smt_ok = (uu___125_4024.smt_ok);
                     tcenv = (uu___125_4024.tcenv);
                     wl_implicits = (uu___125_4024.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4045 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____4045
         then
           let uu____4046 = FStar_Util.string_of_int pid  in
           let uu____4047 =
             let uu____4048 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4048 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4046 uu____4047
         else ());
        commit sol;
        (let uu___126_4055 = wl  in
         {
           attempting = (uu___126_4055.attempting);
           wl_deferred = (uu___126_4055.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___126_4055.defer_ok);
           smt_ok = (uu___126_4055.smt_ok);
           tcenv = (uu___126_4055.tcenv);
           wl_implicits = (uu___126_4055.wl_implicits)
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
             | (uu____4117,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4143 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4143
              in
           (let uu____4149 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____4149
            then
              let uu____4150 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4151 =
                let uu____4152 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4152 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4150 uu____4151
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____4181 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4181 FStar_Util.set_elements  in
      let occurs_ok =
        let uu____4189 =
          FStar_All.pipe_right uvars1
            (FStar_Util.for_some
               (fun uv  ->
                  FStar_Syntax_Unionfind.equiv
                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                    uk.FStar_Syntax_Syntax.ctx_uvar_head))
           in
        Prims.op_Negation uu____4189  in
      let msg =
        if occurs_ok
        then FStar_Pervasives_Native.None
        else
          (let uu____4200 =
             let uu____4201 =
               FStar_Syntax_Print.uvar_to_string
                 uk.FStar_Syntax_Syntax.ctx_uvar_head
                in
             let uu____4202 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
               uu____4201 uu____4202
              in
           FStar_Pervasives_Native.Some uu____4200)
         in
      (uvars1, occurs_ok, msg)
  
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
            let uu____4291 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4291 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4335 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4383  ->
             match uu____4383 with
             | (x,uu____4393) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4406 = FStar_List.last bs  in
      match uu____4406 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4424) ->
          let uu____4429 =
            FStar_Util.prefix_until
              (fun uu___102_4444  ->
                 match uu___102_4444 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4446 -> false) g
             in
          (match uu____4429 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____4459,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____4495 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____4495 with
        | (pfx,uu____4505) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____4517 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____4517 with
             | (uu____4524,src',wl1) ->
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
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
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
      let uu____4604 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4658  ->
                fun uu____4659  ->
                  match (uu____4658, uu____4659) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4740 =
                        let uu____4741 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4741  in
                      if uu____4740
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4766 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4766
                         then
                           let uu____4779 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____4779)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4604 with | (isect,uu____4816) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4845 'Auu____4846 .
    (FStar_Syntax_Syntax.bv,'Auu____4845) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4846) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4903  ->
              fun uu____4904  ->
                match (uu____4903, uu____4904) with
                | ((a,uu____4922),(b,uu____4924)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____4939 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____4939) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____4969  ->
           match uu____4969 with
           | (y,uu____4975) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____4986 'Auu____4987 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4986) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4987)
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
                   let uu____5096 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5096
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5104 =
                        let uu____5107 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5107 :: seen  in
                      aux uu____5104 args2)
               | uu____5108 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____5121 .
    ('Auu____5121,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____5132  ->
    match uu____5132 with
    | (uu____5139,c,args) ->
        let uu____5142 = print_ctx_uvar c  in
        let uu____5143 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____5142 uu____5143
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5149 =
      let uu____5150 = FStar_Syntax_Subst.compress t  in
      uu____5150.FStar_Syntax_Syntax.n  in
    match uu____5149 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5153 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____5154;
           FStar_Syntax_Syntax.pos = uu____5155;
           FStar_Syntax_Syntax.vars = uu____5156;_},uu____5157)
        -> true
    | uu____5178 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> flex_t) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar uv -> (t, uv, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uv;
           FStar_Syntax_Syntax.pos = uu____5196;
           FStar_Syntax_Syntax.vars = uu____5197;_},args)
        -> (t, uv, args)
    | uu____5219 -> failwith "Not a flex-uvar"
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5247 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5284 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5290 -> false
  
let string_of_option :
  'Auu____5297 .
    ('Auu____5297 -> Prims.string) ->
      'Auu____5297 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___103_5312  ->
      match uu___103_5312 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5318 = f x  in Prims.strcat "Some " uu____5318
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___104_5323  ->
    match uu___104_5323 with
    | MisMatch (d1,d2) ->
        let uu____5334 =
          let uu____5335 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5336 =
            let uu____5337 =
              let uu____5338 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5338 ")"  in
            Prims.strcat ") (" uu____5337  in
          Prims.strcat uu____5335 uu____5336  in
        Prims.strcat "MisMatch (" uu____5334
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___105_5343  ->
    match uu___105_5343 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5358 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5388 = m2 ()  in
          (match uu____5388 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5403 -> HeadMatch)
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
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5416 ->
          let uu____5417 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5417 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5428 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5451 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5460 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5488 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5488
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5489 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5490 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5491 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5492 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5505 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5529) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5535,uu____5536) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5578) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5599;
             FStar_Syntax_Syntax.index = uu____5600;
             FStar_Syntax_Syntax.sort = t2;_},uu____5602)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5609 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5610 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5611 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5624 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5631 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5649 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5649
  
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
            let uu____5676 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5676
            then FullMatch
            else
              (let uu____5678 =
                 let uu____5687 =
                   let uu____5690 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5690  in
                 let uu____5691 =
                   let uu____5694 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5694  in
                 (uu____5687, uu____5691)  in
               MisMatch uu____5678)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5700),FStar_Syntax_Syntax.Tm_uinst (g,uu____5702)) ->
            let uu____5711 = head_matches env f g  in
            FStar_All.pipe_right uu____5711 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5714 = FStar_Const.eq_const c d  in
            if uu____5714
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar uv,FStar_Syntax_Syntax.Tm_uvar uv') ->
            let uu____5722 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____5722
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5729),FStar_Syntax_Syntax.Tm_refine (y,uu____5731)) ->
            let uu____5740 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5740 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5742),uu____5743) ->
            let uu____5748 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5748 head_match
        | (uu____5749,FStar_Syntax_Syntax.Tm_refine (x,uu____5751)) ->
            let uu____5756 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5756 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5757,FStar_Syntax_Syntax.Tm_type
           uu____5758) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5759,FStar_Syntax_Syntax.Tm_arrow uu____5760) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5786),FStar_Syntax_Syntax.Tm_app (head',uu____5788))
            ->
            let uu____5829 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5829 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5831),uu____5832) ->
            let uu____5853 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5853 head_match
        | (uu____5854,FStar_Syntax_Syntax.Tm_app (head1,uu____5856)) ->
            let uu____5877 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5877 head_match
        | uu____5878 ->
            let uu____5883 =
              let uu____5892 = delta_depth_of_term env t11  in
              let uu____5895 = delta_depth_of_term env t21  in
              (uu____5892, uu____5895)  in
            MisMatch uu____5883
  
let head_matches_delta :
  'Auu____5912 .
    FStar_TypeChecker_Env.env ->
      'Auu____5912 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
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
            let uu____5951 = FStar_Syntax_Util.head_and_args t  in
            match uu____5951 with
            | (head1,uu____5969) ->
                let uu____5990 =
                  let uu____5991 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5991.FStar_Syntax_Syntax.n  in
                (match uu____5990 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5997 =
                       let uu____5998 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5998 FStar_Option.isSome
                        in
                     if uu____5997
                     then
                       let uu____6017 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6017
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6021 -> FStar_Pervasives_Native.None)
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
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6142)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6160 =
                     let uu____6169 = maybe_inline t11  in
                     let uu____6172 = maybe_inline t21  in
                     (uu____6169, uu____6172)  in
                   match uu____6160 with
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
                (uu____6209,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6227 =
                     let uu____6236 = maybe_inline t11  in
                     let uu____6239 = maybe_inline t21  in
                     (uu____6236, uu____6239)  in
                   match uu____6227 with
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
                when d1 = d2 ->
                let uu____6282 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6282 with
                 | FStar_Pervasives_Native.None  -> fail1 r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11
                        in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
                let uu____6305 =
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
                (match uu____6305 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6329 -> fail1 r
            | uu____6338 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6351 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6351
           then
             let uu____6352 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6353 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6354 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6352
               uu____6353 uu____6354
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6372 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6372 FStar_Pervasives_Native.fst
  
let (rigid_rigid : Prims.int) = (Prims.parse_int "0") 
let (flex_rigid_eq : Prims.int) = (Prims.parse_int "1") 
let (flex_rigid : Prims.int) = (Prims.parse_int "4") 
let (rigid_flex : Prims.int) = (Prims.parse_int "5") 
let (flex_flex : Prims.int) = (Prims.parse_int "7") 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___127_6397 = p  in
      let uu____6400 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6401 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___127_6397.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6400;
        FStar_TypeChecker_Common.relation =
          (uu___127_6397.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6401;
        FStar_TypeChecker_Common.element =
          (uu___127_6397.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___127_6397.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___127_6397.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.scope =
          (uu___127_6397.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___127_6397.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___127_6397.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___127_6397.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6415 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6415
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6420 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6442 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6442 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6450 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6450 with
           | (lh,uu____6470) ->
               let uu____6491 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6491 with
                | (rh,uu____6511) ->
                    let rank =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6533,FStar_Syntax_Syntax.Tm_uvar uu____6534)
                          -> flex_flex
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6535,uu____6536)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> flex_rigid_eq
                      | (uu____6537,FStar_Syntax_Syntax.Tm_uvar uu____6538)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> flex_rigid_eq
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6539,uu____6540)
                          -> flex_rigid
                      | (uu____6541,FStar_Syntax_Syntax.Tm_uvar uu____6542)
                          -> rigid_flex
                      | (uu____6543,uu____6544) -> rigid_rigid  in
                    let uu____6545 =
                      FStar_All.pipe_right
                        (let uu___128_6549 = tp  in
                         {
                           FStar_TypeChecker_Common.pid =
                             (uu___128_6549.FStar_TypeChecker_Common.pid);
                           FStar_TypeChecker_Common.lhs =
                             (uu___128_6549.FStar_TypeChecker_Common.lhs);
                           FStar_TypeChecker_Common.relation =
                             (uu___128_6549.FStar_TypeChecker_Common.relation);
                           FStar_TypeChecker_Common.rhs =
                             (uu___128_6549.FStar_TypeChecker_Common.rhs);
                           FStar_TypeChecker_Common.element =
                             (uu___128_6549.FStar_TypeChecker_Common.element);
                           FStar_TypeChecker_Common.logical_guard =
                             (uu___128_6549.FStar_TypeChecker_Common.logical_guard);
                           FStar_TypeChecker_Common.logical_guard_uvar =
                             (uu___128_6549.FStar_TypeChecker_Common.logical_guard_uvar);
                           FStar_TypeChecker_Common.scope =
                             (uu___128_6549.FStar_TypeChecker_Common.scope);
                           FStar_TypeChecker_Common.reason =
                             (uu___128_6549.FStar_TypeChecker_Common.reason);
                           FStar_TypeChecker_Common.loc =
                             (uu___128_6549.FStar_TypeChecker_Common.loc);
                           FStar_TypeChecker_Common.rank =
                             (FStar_Pervasives_Native.Some rank)
                         })
                        (fun _0_24  -> FStar_TypeChecker_Common.TProb _0_24)
                       in
                    (rank, uu____6545)))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____6555 =
            FStar_All.pipe_right
              (let uu___129_6559 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___129_6559.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___129_6559.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___129_6559.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___129_6559.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___129_6559.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___129_6559.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___129_6559.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.scope =
                   (uu___129_6559.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___129_6559.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___129_6559.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (rigid_rigid, uu____6555)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____6618 probs =
      match uu____6618 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____6671 = rank wl.tcenv hd1  in
               (match uu____6671 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out (m :: tl1)), rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2),
                                 out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2), (m
                                 :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
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
          let uu____6781 = destruct_flex_t t  in
          match uu____6781 with
          | (uu____6782,u,uu____6784) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____6798  ->
                      match uu____6798 with
                      | (y,uu____6804) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____6818  ->
                                  match uu____6818 with
                                  | (x,uu____6824) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____6825 = rank tcenv p  in
        match uu____6825 with
        | (r,p1) ->
            if ((r <> rigid_flex) && (r <> flex_rigid)) && (r <> flex_flex)
            then false
            else
              (match p1 with
               | FStar_TypeChecker_Common.CProb uu____6833 -> false
               | FStar_TypeChecker_Common.TProb p2 ->
                   if r = flex_flex
                   then
                     (flex_will_be_closed p2.FStar_TypeChecker_Common.lhs) ||
                       (flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)
                   else
                     if r = flex_rigid
                     then flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                     else flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____6862 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6876 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6890 -> false
  
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
                        let uu____6942 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____6942 with
                        | (k,uu____6948) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6958 -> false)))
            | uu____6959 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7011 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7017 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7017 = (Prims.parse_int "0")))
                           in
                        if uu____7011 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7033 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7039 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7039 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7033)
               in
            let uu____7040 = filter1 u12  in
            let uu____7043 = filter1 u22  in (uu____7040, uu____7043)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7072 = filter_out_common_univs us1 us2  in
                (match uu____7072 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7131 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7131 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7134 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7144 =
                          let uu____7145 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7146 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7145
                            uu____7146
                           in
                        UFailed uu____7144))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7170 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7170 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7196 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7196 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7199 ->
                let uu____7204 =
                  let uu____7205 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7206 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7205
                    uu____7206 msg
                   in
                UFailed uu____7204
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7207,uu____7208) ->
              let uu____7209 =
                let uu____7210 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7211 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7210 uu____7211
                 in
              failwith uu____7209
          | (FStar_Syntax_Syntax.U_unknown ,uu____7212) ->
              let uu____7213 =
                let uu____7214 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7215 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7214 uu____7215
                 in
              failwith uu____7213
          | (uu____7216,FStar_Syntax_Syntax.U_bvar uu____7217) ->
              let uu____7218 =
                let uu____7219 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7220 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7219 uu____7220
                 in
              failwith uu____7218
          | (uu____7221,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7222 =
                let uu____7223 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7224 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7223 uu____7224
                 in
              failwith uu____7222
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7248 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7248
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7262 = occurs_univ v1 u3  in
              if uu____7262
              then
                let uu____7263 =
                  let uu____7264 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7265 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7264 uu____7265
                   in
                try_umax_components u11 u21 uu____7263
              else
                (let uu____7267 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7267)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7279 = occurs_univ v1 u3  in
              if uu____7279
              then
                let uu____7280 =
                  let uu____7281 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7282 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7281 uu____7282
                   in
                try_umax_components u11 u21 uu____7280
              else
                (let uu____7284 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7284)
          | (FStar_Syntax_Syntax.U_max uu____7285,uu____7286) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7292 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7292
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____7294,FStar_Syntax_Syntax.U_max uu____7295) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7301 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7301
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____7303,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____7304,FStar_Syntax_Syntax.U_name
             uu____7305) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____7306) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____7307) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7308,FStar_Syntax_Syntax.U_succ
             uu____7309) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7310,FStar_Syntax_Syntax.U_zero
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
      let uu____7410 = bc1  in
      match uu____7410 with
      | (bs1,mk_cod1) ->
          let uu____7454 = bc2  in
          (match uu____7454 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____7565 = aux xs ys  in
                     (match uu____7565 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____7648 =
                       let uu____7655 = mk_cod1 xs  in ([], uu____7655)  in
                     let uu____7658 =
                       let uu____7665 = mk_cod2 ys  in ([], uu____7665)  in
                     (uu____7648, uu____7658)
                  in
               aux bs1 bs2)
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____7702 = f  in
      match uu____7702 with
      | (uu____7709,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____7710;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____7711;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____7714;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____7715;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____7716;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____7768  ->
                 match uu____7768 with
                 | (y,uu____7774) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | (uu____7880,[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | ((formal,uu____7912)::formals1,(a,uu____7915)::args2) ->
                let uu____7949 =
                  let uu____7950 = FStar_Syntax_Subst.compress a  in
                  uu____7950.FStar_Syntax_Syntax.n  in
                (match uu____7949 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____7962 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____7962
                     then
                       let uu____7971 =
                         let uu____7974 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____7974 :: pat_binders  in
                       aux uu____7971 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___130_7977 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_7977.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_7977.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____7981 =
                            let uu____7982 =
                              let uu____7989 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____7989)  in
                            FStar_Syntax_Syntax.NT uu____7982  in
                          [uu____7981]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____7996 =
                          let uu____7999 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___131_8002 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_8002.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_8002.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____7999 :: pat_binders  in
                        aux uu____7996 formals2 t_res1 args2)
                 | uu____8003 ->
                     let uu____8004 =
                       let uu____8007 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8007 :: pat_binders  in
                     aux uu____8004 formals1 t_res args2)
            | ([],args2) ->
                let uu____8031 =
                  let uu____8044 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8044  in
                (match uu____8031 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8089 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          let uu____8096 = FStar_Syntax_Util.arrow_formals t_hd  in
          (match uu____8096 with
           | (formals,t_res) -> aux [] formals t_res args)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____8320 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____8320
       then
         let uu____8321 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____8321
       else ());
      (let uu____8323 = next_prob probs  in
       match uu____8323 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___132_8344 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___132_8344.wl_deferred);
               ctr = (uu___132_8344.ctr);
               defer_ok = (uu___132_8344.defer_ok);
               smt_ok = (uu___132_8344.smt_ok);
               tcenv = (uu___132_8344.tcenv);
               wl_implicits = (uu___132_8344.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  (Prims.op_Negation probs1.defer_ok) && (rank1 = flex_rigid)
                then
                  let tp1 =
                    let uu___133_8354 = tp  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___133_8354.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___133_8354.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        FStar_TypeChecker_Common.EQ;
                      FStar_TypeChecker_Common.rhs =
                        (uu___133_8354.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___133_8354.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___133_8354.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___133_8354.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.scope =
                        (uu___133_8354.FStar_TypeChecker_Common.scope);
                      FStar_TypeChecker_Common.reason =
                        (uu___133_8354.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___133_8354.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___133_8354.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env tp1 probs1
                else
                  if
                    (Prims.op_Negation probs1.defer_ok) &&
                      (rigid_flex = rank1)
                  then
                    (let tp1 =
                       let uu___134_8361 = tp  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___134_8361.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___134_8361.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ;
                         FStar_TypeChecker_Common.rhs =
                           (uu___134_8361.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___134_8361.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___134_8361.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___134_8361.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___134_8361.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___134_8361.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___134_8361.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___134_8361.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env tp1 probs1)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____8365,uu____8366) ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____8383 ->
                let uu____8392 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____8451  ->
                          match uu____8451 with
                          | (c,uu____8459,uu____8460) -> c < probs.ctr))
                   in
                (match uu____8392 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____8501 =
                            let uu____8506 =
                              FStar_List.map
                                (fun uu____8521  ->
                                   match uu____8521 with
                                   | (uu____8532,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____8506, (probs.wl_implicits))  in
                          Success uu____8501
                      | uu____8535 ->
                          let uu____8544 =
                            let uu___135_8545 = probs  in
                            let uu____8546 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____8565  ->
                                      match uu____8565 with
                                      | (uu____8572,uu____8573,y) -> y))
                               in
                            {
                              attempting = uu____8546;
                              wl_deferred = rest;
                              ctr = (uu___135_8545.ctr);
                              defer_ok = (uu___135_8545.defer_ok);
                              smt_ok = (uu___135_8545.smt_ok);
                              tcenv = (uu___135_8545.tcenv);
                              wl_implicits = (uu___135_8545.wl_implicits)
                            }  in
                          solve env uu____8544))))

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
            let uu____8580 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____8580 with
            | USolved wl1 ->
                let uu____8582 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____8582
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
                  let uu____8634 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____8634 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____8637 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____8649;
                  FStar_Syntax_Syntax.vars = uu____8650;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____8653;
                  FStar_Syntax_Syntax.vars = uu____8654;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____8666,uu____8667) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____8674,FStar_Syntax_Syntax.Tm_uinst uu____8675) ->
                failwith "Impossible: expect head symbols to match"
            | uu____8682 -> USolved wl

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
            ((let uu____8692 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____8692
              then
                let uu____8693 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____8693 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

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
              (let uu____8717 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____8717
               then
                 let uu____8718 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____8719 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____8718 (rel_to_string (p_rel orig)) uu____8719
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____8820 = rhs wl1 scope env1 subst1  in
                     (match uu____8820 with
                      | (rhs_prob,wl2) ->
                          ((let uu____8840 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____8840
                            then
                              let uu____8841 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____8841
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___136_8899 = hd1  in
                       let uu____8900 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___136_8899.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___136_8899.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____8900
                       }  in
                     let hd21 =
                       let uu___137_8904 = hd2  in
                       let uu____8905 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___137_8904.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___137_8904.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____8905
                       }  in
                     let uu____8908 =
                       let uu____8913 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____8913
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____8908 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____8932 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____8932
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____8936 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____8936 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____8991 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____8991
                                  in
                               ((let uu____8993 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8993
                                 then
                                   let uu____8994 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____8995 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____8994
                                     uu____8995
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____9030 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let scope = p_scope orig  in
               let uu____9066 = aux wl scope env [] bs1 bs2  in
               match uu____9066 with
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
        (let uu____9113 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____9113 wl)

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
              let uu____9127 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____9127 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____9157 = lhs1  in
              match uu____9157 with
              | (uu____9160,ctx_u,uu____9162) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____9168 ->
                        let uu____9169 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____9169 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____9216 = quasi_pattern env1 lhs1  in
              match uu____9216 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____9246) ->
                  let uu____9251 = lhs1  in
                  (match uu____9251 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____9265 = occurs_check ctx_u rhs1  in
                       (match uu____9265 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____9307 =
                                let uu____9314 =
                                  let uu____9315 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____9315
                                   in
                                FStar_Util.Inl uu____9314  in
                              (uu____9307, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____9335 =
                                 let uu____9336 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____9336  in
                               if uu____9335
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____9356 =
                                    let uu____9363 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____9363  in
                                  let uu____9368 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____9356, uu____9368)))))
               in
            let copy_uvar u t wl1 =
              new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl1
                u.FStar_Syntax_Syntax.ctx_uvar_range
                u.FStar_Syntax_Syntax.ctx_uvar_gamma
                u.FStar_Syntax_Syntax.ctx_uvar_binders t
                u.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            let imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs arrow1 =
              let uu____9437 = lhs1  in
              match uu____9437 with
              | (uu____9438,u_lhs,uu____9440) ->
                  let imitate_comp bs bs_terms c wl2 =
                    let imitate_tot_or_gtot t uopt f wl3 =
                      let uu____9541 =
                        match uopt with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Util.type_u ()
                        | FStar_Pervasives_Native.Some univ ->
                            let uu____9551 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_type univ)
                                FStar_Pervasives_Native.None
                                t.FStar_Syntax_Syntax.pos
                               in
                            (uu____9551, univ)
                         in
                      match uu____9541 with
                      | (k,univ) ->
                          let uu____9564 =
                            let uu____9571 =
                              let uu____9574 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.arrow bs uu____9574  in
                            copy_uvar u_lhs uu____9571 wl3  in
                          (match uu____9564 with
                           | (uu____9581,u,wl4) ->
                               let uu____9584 =
                                 let uu____9587 =
                                   FStar_Syntax_Syntax.mk_Tm_app u bs_terms
                                     FStar_Pervasives_Native.None
                                     c.FStar_Syntax_Syntax.pos
                                    in
                                 f uu____9587
                                   (FStar_Pervasives_Native.Some univ)
                                  in
                               (uu____9584, wl4))
                       in
                    match c.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Total (t,uopt) ->
                        imitate_tot_or_gtot t uopt
                          FStar_Syntax_Syntax.mk_Total' wl2
                    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                        imitate_tot_or_gtot t uopt
                          FStar_Syntax_Syntax.mk_GTotal' wl2
                    | FStar_Syntax_Syntax.Comp ct ->
                        let uu____9619 =
                          let uu____9632 =
                            let uu____9641 =
                              FStar_Syntax_Syntax.as_arg
                                ct.FStar_Syntax_Syntax.result_typ
                               in
                            uu____9641 ::
                              (ct.FStar_Syntax_Syntax.effect_args)
                             in
                          FStar_List.fold_right
                            (fun uu____9687  ->
                               fun uu____9688  ->
                                 match (uu____9687, uu____9688) with
                                 | ((a,i),(out_args,wl3)) ->
                                     let uu____9779 =
                                       let uu____9786 =
                                         let uu____9789 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_left
                                           FStar_Pervasives_Native.fst
                                           uu____9789
                                          in
                                       copy_uvar u_lhs uu____9786 wl3  in
                                     (match uu____9779 with
                                      | (uu____9812,t_a,wl4) ->
                                          let uu____9815 =
                                            let uu____9822 =
                                              let uu____9825 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_a
                                                 in
                                              FStar_Syntax_Util.arrow bs
                                                uu____9825
                                               in
                                            copy_uvar u_lhs uu____9822 wl4
                                             in
                                          (match uu____9815 with
                                           | (uu____9838,a',wl5) ->
                                               let a'1 =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   a' bs_terms
                                                   FStar_Pervasives_Native.None
                                                   a.FStar_Syntax_Syntax.pos
                                                  in
                                               (((a'1, i) :: out_args), wl5))))
                            uu____9632 ([], wl2)
                           in
                        (match uu____9619 with
                         | (out_args,wl3) ->
                             let ct' =
                               let uu___138_9899 = ct  in
                               let uu____9900 =
                                 let uu____9903 = FStar_List.hd out_args  in
                                 FStar_Pervasives_Native.fst uu____9903  in
                               let uu____9918 = FStar_List.tl out_args  in
                               {
                                 FStar_Syntax_Syntax.comp_univs =
                                   (uu___138_9899.FStar_Syntax_Syntax.comp_univs);
                                 FStar_Syntax_Syntax.effect_name =
                                   (uu___138_9899.FStar_Syntax_Syntax.effect_name);
                                 FStar_Syntax_Syntax.result_typ = uu____9900;
                                 FStar_Syntax_Syntax.effect_args = uu____9918;
                                 FStar_Syntax_Syntax.flags =
                                   (uu___138_9899.FStar_Syntax_Syntax.flags)
                               }  in
                             ((let uu___139_9936 = c  in
                               {
                                 FStar_Syntax_Syntax.n =
                                   (FStar_Syntax_Syntax.Comp ct');
                                 FStar_Syntax_Syntax.pos =
                                   (uu___139_9936.FStar_Syntax_Syntax.pos);
                                 FStar_Syntax_Syntax.vars =
                                   (uu___139_9936.FStar_Syntax_Syntax.vars)
                               }), wl3))
                     in
                  let uu____9939 =
                    FStar_Syntax_Util.arrow_formals_comp arrow1  in
                  (match uu____9939 with
                   | (formals,c) ->
                       let rec aux bs bs_terms formals1 wl2 =
                         match formals1 with
                         | [] ->
                             let uu____9993 = imitate_comp bs bs_terms c wl2
                                in
                             (match uu____9993 with
                              | (c',wl3) ->
                                  let lhs' = FStar_Syntax_Util.arrow bs c'
                                     in
                                  let sol =
                                    let uu____10010 =
                                      let uu____10015 =
                                        FStar_Syntax_Util.abs bs_lhs lhs'
                                          (FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Util.residual_tot
                                                t_res_lhs))
                                         in
                                      (u_lhs, uu____10015)  in
                                    TERM uu____10010  in
                                  let uu____10016 =
                                    let uu____10021 = p_scope orig1  in
                                    mk_t_problem wl3 uu____10021 orig1 lhs'
                                      FStar_TypeChecker_Common.EQ rhs
                                      FStar_Pervasives_Native.None
                                      "arrow imitation"
                                     in
                                  (match uu____10016 with
                                   | (sub_prob,wl4) ->
                                       let uu____10024 =
                                         let uu____10025 =
                                           solve_prob orig1
                                             FStar_Pervasives_Native.None
                                             [sol] wl4
                                            in
                                         attempt [sub_prob] uu____10025  in
                                       solve env1 uu____10024))
                         | (x,imp)::formals2 ->
                             let uu____10039 =
                               let uu____10046 =
                                 let uu____10049 =
                                   let uu____10050 =
                                     let uu____10051 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____10051
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Syntax.mk_Total uu____10050
                                    in
                                 FStar_Syntax_Util.arrow bs uu____10049  in
                               copy_uvar u_lhs uu____10046 wl2  in
                             (match uu____10039 with
                              | (ctx_u_x,u_x,wl3) ->
                                  let t_y =
                                    FStar_Syntax_Syntax.mk_Tm_app u_x
                                      bs_terms FStar_Pervasives_Native.None
                                      (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                     in
                                  let y =
                                    let uu____10067 =
                                      let uu____10070 =
                                        FStar_Syntax_Syntax.range_of_bv x  in
                                      FStar_Pervasives_Native.Some
                                        uu____10070
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____10067
                                      t_y
                                     in
                                  let uu____10071 =
                                    let uu____10074 =
                                      let uu____10077 =
                                        let uu____10078 =
                                          FStar_Syntax_Syntax.bv_to_name y
                                           in
                                        (uu____10078, imp)  in
                                      [uu____10077]  in
                                    FStar_List.append bs_terms uu____10074
                                     in
                                  aux (FStar_List.append bs [(y, imp)])
                                    uu____10071 formals2 wl3)
                          in
                       aux [] [] formals wl1)
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____10131 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____10131 with
              | (rhs_hd,args) ->
                  let uu____10168 = FStar_Util.prefix args  in
                  (match uu____10168 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____10226 = lhs1  in
                       (match uu____10226 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____10230 =
                              let uu____10237 =
                                let uu____10244 =
                                  let uu____10247 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____10247
                                   in
                                copy_uvar u_lhs uu____10244 wl1  in
                              match uu____10237 with
                              | (uu____10264,t_last_arg,wl2) ->
                                  let uu____10267 =
                                    let uu____10274 =
                                      let uu____10277 =
                                        let uu____10284 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____10284]  in
                                      let uu____10297 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____10277
                                        uu____10297
                                       in
                                    copy_uvar u_lhs uu____10274 wl2  in
                                  (match uu____10267 with
                                   | (uu____10304,lhs',wl3) ->
                                       let uu____10307 =
                                         copy_uvar u_lhs t_last_arg wl3  in
                                       (match uu____10307 with
                                        | (uu____10320,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____10230 with
                             | (lhs',lhs'_last_arg,_wl) ->
                                 let sol =
                                   let uu____10329 =
                                     let uu____10330 =
                                       let uu____10335 =
                                         let uu____10336 =
                                           let uu____10339 =
                                             let uu____10344 =
                                               let uu____10345 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____10345]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____10344
                                              in
                                           uu____10339
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____10336
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____10335)  in
                                     TERM uu____10330  in
                                   [uu____10329]  in
                                 let uu____10366 =
                                   let uu____10373 =
                                     let uu____10378 = p_scope orig1  in
                                     mk_t_problem wl1 uu____10378 orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____10373 with
                                   | (p1,wl2) ->
                                       let uu____10387 =
                                         let uu____10392 = p_scope orig1  in
                                         mk_t_problem wl2 uu____10392 orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____10387 with
                                        | (p2,wl3) -> ([p1; p2], wl3))
                                    in
                                 (match uu____10366 with
                                  | (sub_probs,wl2) ->
                                      let uu____10411 =
                                        let uu____10412 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl2
                                           in
                                        attempt sub_probs uu____10412  in
                                      solve env1 uu____10411))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____10445 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____10445 with
                | (uu____10460,args) ->
                    (match args with | [] -> false | uu____10488 -> true)
                 in
              let is_arrow rhs2 =
                let uu____10503 =
                  let uu____10504 = FStar_Syntax_Subst.compress rhs2  in
                  uu____10504.FStar_Syntax_Syntax.n  in
                match uu____10503 with
                | FStar_Syntax_Syntax.Tm_arrow uu____10507 -> true
                | uu____10520 -> false  in
              let uu____10521 = quasi_pattern env1 lhs1  in
              match uu____10521 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10532 =
                    let uu____10533 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____10533
                     in
                  giveup_or_defer env1 orig1 wl1 uu____10532
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____10540 = is_app rhs1  in
                  if uu____10540
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____10542 = is_arrow rhs1  in
                     if uu____10542
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         rhs1
                     else
                       (let uu____10544 =
                          let uu____10545 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____10545
                           in
                        giveup_or_defer env1 orig1 wl1 uu____10544))
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
                let uu____10548 = lhs  in
                (match uu____10548 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____10552 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____10552 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____10567 =
                              let uu____10570 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____10570
                               in
                            FStar_All.pipe_right uu____10567
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____10585 = occurs_check ctx_uv rhs1  in
                          (match uu____10585 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____10607 =
                                   let uu____10608 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____10608
                                    in
                                 giveup_or_defer env orig wl uu____10607
                               else
                                 (let uu____10610 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____10610
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____10615 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____10615
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____10617 =
                                         let uu____10618 =
                                           names_to_string1 fvs2  in
                                         let uu____10619 =
                                           names_to_string1 fvs1  in
                                         let uu____10620 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____10618 uu____10619
                                           uu____10620
                                          in
                                       giveup_or_defer env orig wl
                                         uu____10617)
                                    else first_order orig env wl lhs rhs1))
                      | uu____10626 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____10630 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____10630 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____10653 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____10653
                             | (FStar_Util.Inl msg,uu____10655) ->
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
                let uu____10671 =
                  let uu____10688 = quasi_pattern env lhs  in
                  let uu____10695 = quasi_pattern env rhs  in
                  (uu____10688, uu____10695)  in
                (match uu____10671 with
                 | (FStar_Pervasives_Native.Some
                    (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                    (binders_rhs,t_res_rhs)) ->
                     let uu____10738 = lhs  in
                     (match uu____10738 with
                      | ({ FStar_Syntax_Syntax.n = uu____10739;
                           FStar_Syntax_Syntax.pos = range;
                           FStar_Syntax_Syntax.vars = uu____10741;_},u_lhs,uu____10743)
                          ->
                          let uu____10746 = rhs  in
                          (match uu____10746 with
                           | (uu____10747,u_rhs,uu____10749) ->
                               let uu____10750 =
                                 (FStar_Syntax_Unionfind.equiv
                                    u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                   && (binders_eq binders_lhs binders_rhs)
                                  in
                               if uu____10750
                               then
                                 let uu____10751 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None [] wl
                                    in
                                 solve env uu____10751
                               else
                                 (let uu____10753 =
                                    let uu____10758 = p_scope orig  in
                                    mk_t_problem wl uu____10758 orig
                                      t_res_lhs FStar_TypeChecker_Common.EQ
                                      t_res_rhs FStar_Pervasives_Native.None
                                      "flex-flex typing"
                                     in
                                  match uu____10753 with
                                  | (sub_prob,wl1) ->
                                      let uu____10761 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      (match uu____10761 with
                                       | (ctx_w,(ctx_l,ctx_r)) ->
                                           let gamma_w =
                                             gamma_until
                                               u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                               ctx_w
                                              in
                                           let zs =
                                             intersect_binders
                                               (FStar_List.append ctx_l
                                                  binders_lhs)
                                               (FStar_List.append ctx_r
                                                  binders_rhs)
                                              in
                                           let uu____10789 =
                                             let uu____10796 =
                                               let uu____10799 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t_res_lhs
                                                  in
                                               FStar_Syntax_Util.arrow zs
                                                 uu____10799
                                                in
                                             new_uvar
                                               (Prims.strcat
                                                  "flex-flex quasi: lhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat ", rhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                               wl1 range gamma_w ctx_w
                                               uu____10796
                                               (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                  ||
                                                  u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                              in
                                           (match uu____10789 with
                                            | (uu____10800,w,wl2) ->
                                                let w_app =
                                                  let uu____10806 =
                                                    let uu____10811 =
                                                      FStar_List.map
                                                        (fun uu____10820  ->
                                                           match uu____10820
                                                           with
                                                           | (z,uu____10826)
                                                               ->
                                                               let uu____10827
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   z
                                                                  in
                                                               FStar_Syntax_Syntax.as_arg
                                                                 uu____10827)
                                                        zs
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      w uu____10811
                                                     in
                                                  uu____10806
                                                    FStar_Pervasives_Native.None
                                                    w.FStar_Syntax_Syntax.pos
                                                   in
                                                ((let uu____10831 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env)
                                                      (FStar_Options.Other
                                                         "RelCheck")
                                                     in
                                                  if uu____10831
                                                  then
                                                    let uu____10832 =
                                                      flex_t_to_string lhs
                                                       in
                                                    let uu____10833 =
                                                      flex_t_to_string rhs
                                                       in
                                                    let uu____10834 =
                                                      let uu____10835 =
                                                        destruct_flex_t w  in
                                                      flex_t_to_string
                                                        uu____10835
                                                       in
                                                    FStar_Util.print3
                                                      "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                      uu____10832 uu____10833
                                                      uu____10834
                                                  else ());
                                                 (let sol =
                                                    let s1 =
                                                      let uu____10847 =
                                                        let uu____10852 =
                                                          FStar_Syntax_Util.abs
                                                            binders_lhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_lhs, uu____10852)
                                                         in
                                                      TERM uu____10847  in
                                                    let uu____10853 =
                                                      FStar_Syntax_Unionfind.equiv
                                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       in
                                                    if uu____10853
                                                    then [s1]
                                                    else
                                                      (let s2 =
                                                         let uu____10858 =
                                                           let uu____10863 =
                                                             FStar_Syntax_Util.abs
                                                               binders_rhs
                                                               w_app
                                                               (FStar_Pervasives_Native.Some
                                                                  (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                              in
                                                           (u_rhs,
                                                             uu____10863)
                                                            in
                                                         TERM uu____10858  in
                                                       [s1; s2])
                                                     in
                                                  let uu____10864 =
                                                    let uu____10865 =
                                                      solve_prob orig
                                                        FStar_Pervasives_Native.None
                                                        sol wl2
                                                       in
                                                    attempt [sub_prob]
                                                      uu____10865
                                                     in
                                                  solve env uu____10864)))))))
                 | uu____10866 ->
                     giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____10934 = head_matches_delta env1 wl1 t1 t2  in
           match uu____10934 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____10965,uu____10966) ->
                    let rec may_relate head3 =
                      let uu____10993 =
                        let uu____10994 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10994.FStar_Syntax_Syntax.n  in
                      match uu____10993 with
                      | FStar_Syntax_Syntax.Tm_name uu____10997 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____10998 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____11021;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____11022;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____11025;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____11026;
                            FStar_Syntax_Syntax.fv_qual = uu____11027;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____11031,uu____11032) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____11074) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____11080) ->
                          may_relate t
                      | uu____11085 -> false  in
                    let uu____11086 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____11086
                    then
                      let uu____11087 =
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
                                 let uu____11115 =
                                   let uu____11116 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____11116 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____11115
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____11121 = has_type_guard t1 t2  in
                             (uu____11121, wl1)
                           else
                             (let uu____11127 = has_type_guard t2 t1  in
                              (uu____11127, wl1)))
                         in
                      (match uu____11087 with
                       | (guard,wl2) ->
                           let uu____11134 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____11134)
                    else
                      (let uu____11136 =
                         let uu____11137 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____11138 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____11137 uu____11138
                          in
                       giveup env1 uu____11136 orig)
                | (uu____11139,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___140_11153 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___140_11153.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___140_11153.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___140_11153.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___140_11153.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___140_11153.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___140_11153.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___140_11153.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___140_11153.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___140_11153.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____11154,FStar_Pervasives_Native.None ) ->
                    ((let uu____11166 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11166
                      then
                        let uu____11167 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____11168 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____11169 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____11170 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____11167
                          uu____11168 uu____11169 uu____11170
                      else ());
                     (let uu____11172 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____11172 with
                      | (head11,args1) ->
                          let uu____11209 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____11209 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____11263 =
                                   let uu____11264 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____11265 = args_to_string args1  in
                                   let uu____11266 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____11267 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____11264 uu____11265 uu____11266
                                     uu____11267
                                    in
                                 giveup env1 uu____11263 orig
                               else
                                 (let uu____11269 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____11275 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____11275 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____11269
                                  then
                                    let uu____11276 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____11276 with
                                    | USolved wl2 ->
                                        let uu____11278 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____11278
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____11282 =
                                       base_and_refinement env1 t1  in
                                     match uu____11282 with
                                     | (base1,refinement1) ->
                                         let uu____11307 =
                                           base_and_refinement env1 t2  in
                                         (match uu____11307 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____11364 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____11364 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____11368 =
                                                          FStar_List.fold_right2
                                                            (fun uu____11401 
                                                               ->
                                                               fun
                                                                 uu____11402 
                                                                 ->
                                                                 fun
                                                                   uu____11403
                                                                    ->
                                                                   match 
                                                                    (uu____11401,
                                                                    uu____11402,
                                                                    uu____11403)
                                                                   with
                                                                   | 
                                                                   ((a,uu____11439),
                                                                    (a',uu____11441),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____11462
                                                                    =
                                                                    let uu____11467
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_t_problem
                                                                    wl3
                                                                    uu____11467
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____11462
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
                                                        (match uu____11368
                                                         with
                                                         | (subprobs,wl3) ->
                                                             let formula =
                                                               let uu____11487
                                                                 =
                                                                 FStar_List.map
                                                                   (fun p  ->
                                                                    p_guard p)
                                                                   subprobs
                                                                  in
                                                               FStar_Syntax_Util.mk_conj_l
                                                                 uu____11487
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
                                                                  wl4)))
                                               | uu____11493 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___141_11533 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___141_11533.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____11536 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____11536
          then
            let uu____11537 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____11537
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____11541 = FStar_Util.physical_equality t1 t2  in
             if uu____11541
             then
               let uu____11542 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____11542
             else
               ((let uu____11545 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____11545
                 then
                   let uu____11546 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____11547 = FStar_Syntax_Print.tag_of_term t2  in
                   let uu____11548 = prob_to_string env orig  in
                   FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____11546
                     uu____11547 uu____11548
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____11551,uu____11552)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____11577,FStar_Syntax_Syntax.Tm_delayed uu____11578)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____11603,uu____11604)
                     ->
                     let uu____11631 =
                       let uu___142_11632 = problem  in
                       let uu____11633 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___142_11632.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11633;
                         FStar_TypeChecker_Common.relation =
                           (uu___142_11632.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___142_11632.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___142_11632.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___142_11632.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___142_11632.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___142_11632.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___142_11632.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___142_11632.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___142_11632.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____11631 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____11634,uu____11635) ->
                     let uu____11642 =
                       let uu___143_11643 = problem  in
                       let uu____11644 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___143_11643.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11644;
                         FStar_TypeChecker_Common.relation =
                           (uu___143_11643.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___143_11643.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___143_11643.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___143_11643.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___143_11643.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___143_11643.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___143_11643.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___143_11643.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___143_11643.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____11642 wl
                 | (uu____11645,FStar_Syntax_Syntax.Tm_ascribed uu____11646)
                     ->
                     let uu____11673 =
                       let uu___144_11674 = problem  in
                       let uu____11675 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___144_11674.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___144_11674.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___144_11674.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11675;
                         FStar_TypeChecker_Common.element =
                           (uu___144_11674.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___144_11674.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___144_11674.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___144_11674.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___144_11674.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___144_11674.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___144_11674.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____11673 wl
                 | (uu____11676,FStar_Syntax_Syntax.Tm_meta uu____11677) ->
                     let uu____11684 =
                       let uu___145_11685 = problem  in
                       let uu____11686 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___145_11685.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___145_11685.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___145_11685.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11686;
                         FStar_TypeChecker_Common.element =
                           (uu___145_11685.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___145_11685.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___145_11685.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___145_11685.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___145_11685.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___145_11685.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___145_11685.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____11684 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____11688),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____11690)) ->
                     let uu____11699 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____11699
                 | (FStar_Syntax_Syntax.Tm_bvar uu____11700,uu____11701) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____11702,FStar_Syntax_Syntax.Tm_bvar uu____11703) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___106_11760 =
                       match uu___106_11760 with
                       | [] -> c
                       | bs ->
                           let uu____11780 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____11780
                        in
                     let uu____11789 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____11789 with
                      | ((bs11,c11),(bs21,c21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun wl1  ->
                               fun scope  ->
                                 fun env1  ->
                                   fun subst1  ->
                                     let c12 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         c11
                                        in
                                     let c22 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         c21
                                        in
                                     let rel =
                                       let uu____11912 =
                                         FStar_Options.use_eq_at_higher_order
                                           ()
                                          in
                                       if uu____11912
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
                     let mk_t t l uu___107_11987 =
                       match uu___107_11987 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____12021 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____12021 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun wl1  ->
                               fun scope  ->
                                 fun env1  ->
                                   fun subst1  ->
                                     let uu____12140 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____12141 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_t_problem wl1 scope orig uu____12140
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____12141
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"))
                 | (FStar_Syntax_Syntax.Tm_abs uu____12142,uu____12143) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____12170 -> true
                       | uu____12187 -> false  in
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
                         (let uu____12224 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___146_12232 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___146_12232.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___146_12232.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___146_12232.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___146_12232.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___146_12232.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___146_12232.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___146_12232.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___146_12232.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___146_12232.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___146_12232.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___146_12232.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___146_12232.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___146_12232.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___146_12232.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___146_12232.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___146_12232.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___146_12232.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___146_12232.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___146_12232.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___146_12232.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___146_12232.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___146_12232.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___146_12232.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___146_12232.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___146_12232.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___146_12232.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___146_12232.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___146_12232.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___146_12232.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___146_12232.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___146_12232.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___146_12232.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___146_12232.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___146_12232.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___146_12232.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____12224 with
                          | (uu____12233,ty,uu____12235) ->
                              let uu____12236 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____12236)
                        in
                     let uu____12237 =
                       let uu____12250 = maybe_eta t1  in
                       let uu____12255 = maybe_eta t2  in
                       (uu____12250, uu____12255)  in
                     (match uu____12237 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___147_12279 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___147_12279.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___147_12279.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___147_12279.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___147_12279.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___147_12279.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.scope =
                                 (uu___147_12279.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___147_12279.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___147_12279.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___147_12279.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____12290 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____12290
                          then
                            let uu____12291 = destruct_flex_t not_abs  in
                            solve_t_flex_rigid_eq env orig wl uu____12291
                              t_abs
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___148_12296 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___148_12296.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___148_12296.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___148_12296.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___148_12296.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.logical_guard_uvar
                                      =
                                      (uu___148_12296.FStar_TypeChecker_Common.logical_guard_uvar);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___148_12296.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___148_12296.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___148_12296.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___148_12296.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____12308 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____12308
                          then
                            let uu____12309 = destruct_flex_t not_abs  in
                            solve_t_flex_rigid_eq env orig wl uu____12309
                              t_abs
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___148_12314 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___148_12314.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___148_12314.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___148_12314.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___148_12314.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.logical_guard_uvar
                                      =
                                      (uu___148_12314.FStar_TypeChecker_Common.logical_guard_uvar);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___148_12314.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___148_12314.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___148_12314.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___148_12314.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____12316 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____12329,FStar_Syntax_Syntax.Tm_abs uu____12330) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____12357 -> true
                       | uu____12374 -> false  in
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
                         (let uu____12411 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___146_12419 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___146_12419.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___146_12419.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___146_12419.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___146_12419.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___146_12419.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___146_12419.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___146_12419.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___146_12419.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___146_12419.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___146_12419.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___146_12419.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___146_12419.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___146_12419.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___146_12419.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___146_12419.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___146_12419.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___146_12419.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___146_12419.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___146_12419.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___146_12419.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___146_12419.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___146_12419.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___146_12419.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___146_12419.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___146_12419.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___146_12419.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___146_12419.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___146_12419.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___146_12419.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___146_12419.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___146_12419.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___146_12419.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___146_12419.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___146_12419.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___146_12419.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____12411 with
                          | (uu____12420,ty,uu____12422) ->
                              let uu____12423 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____12423)
                        in
                     let uu____12424 =
                       let uu____12437 = maybe_eta t1  in
                       let uu____12442 = maybe_eta t2  in
                       (uu____12437, uu____12442)  in
                     (match uu____12424 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___147_12466 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___147_12466.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___147_12466.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___147_12466.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___147_12466.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___147_12466.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.scope =
                                 (uu___147_12466.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___147_12466.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___147_12466.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___147_12466.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____12477 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____12477
                          then
                            let uu____12478 = destruct_flex_t not_abs  in
                            solve_t_flex_rigid_eq env orig wl uu____12478
                              t_abs
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___148_12483 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___148_12483.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___148_12483.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___148_12483.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___148_12483.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.logical_guard_uvar
                                      =
                                      (uu___148_12483.FStar_TypeChecker_Common.logical_guard_uvar);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___148_12483.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___148_12483.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___148_12483.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___148_12483.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____12495 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____12495
                          then
                            let uu____12496 = destruct_flex_t not_abs  in
                            solve_t_flex_rigid_eq env orig wl uu____12496
                              t_abs
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___148_12501 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___148_12501.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___148_12501.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___148_12501.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___148_12501.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.logical_guard_uvar
                                      =
                                      (uu___148_12501.FStar_TypeChecker_Common.logical_guard_uvar);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___148_12501.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___148_12501.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___148_12501.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___148_12501.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____12503 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____12531 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____12531) &&
                          (let uu____12535 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____12535))
                         &&
                         (let uu____12542 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____12542 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___108_12554 =
                                match uu___108_12554 with
                                | FStar_Syntax_Syntax.Delta_constant  -> true
                                | FStar_Syntax_Syntax.Delta_defined_at_level
                                    uu____12555 -> true
                                | uu____12556 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____12557 -> false)
                        in
                     let uu____12558 = as_refinement should_delta env wl t1
                        in
                     (match uu____12558 with
                      | (x11,phi1) ->
                          let uu____12565 =
                            as_refinement should_delta env wl t2  in
                          (match uu____12565 with
                           | (x21,phi21) ->
                               let uu____12572 =
                                 let uu____12577 = p_scope orig  in
                                 mk_t_problem wl uu____12577 orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               (match uu____12572 with
                                | (base_prob,wl1) ->
                                    let x12 =
                                      FStar_Syntax_Syntax.freshen_bv x11  in
                                    let subst1 =
                                      [FStar_Syntax_Syntax.DB
                                         ((Prims.parse_int "0"), x12)]
                                       in
                                    let phi11 =
                                      FStar_Syntax_Subst.subst subst1 phi1
                                       in
                                    let phi22 =
                                      FStar_Syntax_Subst.subst subst1 phi21
                                       in
                                    let env1 =
                                      FStar_TypeChecker_Env.push_bv env x12
                                       in
                                    let mk_imp1 imp phi12 phi23 =
                                      let uu____12621 = imp phi12 phi23  in
                                      FStar_All.pipe_right uu____12621
                                        (guard_on_element wl1 problem x12)
                                       in
                                    let fallback uu____12627 =
                                      let impl =
                                        if
                                          problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ
                                        then
                                          mk_imp1 FStar_Syntax_Util.mk_iff
                                            phi11 phi22
                                        else
                                          mk_imp1 FStar_Syntax_Util.mk_imp
                                            phi11 phi22
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
                                      solve env1 (attempt [base_prob] wl2)
                                       in
                                    if
                                      problem.FStar_TypeChecker_Common.relation
                                        = FStar_TypeChecker_Common.EQ
                                    then
                                      let uu____12634 =
                                        let uu____12639 =
                                          let uu____12640 = p_scope orig  in
                                          let uu____12647 =
                                            let uu____12654 =
                                              FStar_Syntax_Syntax.mk_binder
                                                x12
                                               in
                                            [uu____12654]  in
                                          FStar_List.append uu____12640
                                            uu____12647
                                           in
                                        mk_t_problem wl1 uu____12639 orig
                                          phi11 FStar_TypeChecker_Common.EQ
                                          phi22 FStar_Pervasives_Native.None
                                          "refinement formula"
                                         in
                                      (match uu____12634 with
                                       | (ref_prob,wl2) ->
                                           let uu____12673 =
                                             solve env1
                                               (let uu___149_12675 = wl2  in
                                                {
                                                  attempting = [ref_prob];
                                                  wl_deferred = [];
                                                  ctr = (uu___149_12675.ctr);
                                                  defer_ok = false;
                                                  smt_ok =
                                                    (uu___149_12675.smt_ok);
                                                  tcenv =
                                                    (uu___149_12675.tcenv);
                                                  wl_implicits =
                                                    (uu___149_12675.wl_implicits)
                                                })
                                              in
                                           (match uu____12673 with
                                            | Failed uu____12682 ->
                                                fallback ()
                                            | Success uu____12687 ->
                                                let guard =
                                                  let uu____12695 =
                                                    FStar_All.pipe_right
                                                      (p_guard ref_prob)
                                                      (guard_on_element wl2
                                                         problem x12)
                                                     in
                                                  FStar_Syntax_Util.mk_conj
                                                    (p_guard base_prob)
                                                    uu____12695
                                                   in
                                                let wl3 =
                                                  solve_prob orig
                                                    (FStar_Pervasives_Native.Some
                                                       guard) [] wl2
                                                   in
                                                let wl4 =
                                                  let uu___150_12698 = wl3
                                                     in
                                                  {
                                                    attempting =
                                                      (uu___150_12698.attempting);
                                                    wl_deferred =
                                                      (uu___150_12698.wl_deferred);
                                                    ctr =
                                                      (wl3.ctr +
                                                         (Prims.parse_int "1"));
                                                    defer_ok =
                                                      (uu___150_12698.defer_ok);
                                                    smt_ok =
                                                      (uu___150_12698.smt_ok);
                                                    tcenv =
                                                      (uu___150_12698.tcenv);
                                                    wl_implicits =
                                                      (uu___150_12698.wl_implicits)
                                                  }  in
                                                solve env1
                                                  (attempt [base_prob] wl4)))
                                    else fallback ())))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____12700,FStar_Syntax_Syntax.Tm_uvar uu____12701) ->
                     let uu____12702 = destruct_flex_t t1  in
                     let uu____12703 = destruct_flex_t t2  in
                     solve_t_flex_flex env orig wl uu____12702 uu____12703
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12704;
                       FStar_Syntax_Syntax.pos = uu____12705;
                       FStar_Syntax_Syntax.vars = uu____12706;_},uu____12707),FStar_Syntax_Syntax.Tm_uvar
                    uu____12708) ->
                     let uu____12729 = destruct_flex_t t1  in
                     let uu____12730 = destruct_flex_t t2  in
                     solve_t_flex_flex env orig wl uu____12729 uu____12730
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____12731,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12732;
                       FStar_Syntax_Syntax.pos = uu____12733;
                       FStar_Syntax_Syntax.vars = uu____12734;_},uu____12735))
                     ->
                     let uu____12756 = destruct_flex_t t1  in
                     let uu____12757 = destruct_flex_t t2  in
                     solve_t_flex_flex env orig wl uu____12756 uu____12757
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12758;
                       FStar_Syntax_Syntax.pos = uu____12759;
                       FStar_Syntax_Syntax.vars = uu____12760;_},uu____12761),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12762;
                       FStar_Syntax_Syntax.pos = uu____12763;
                       FStar_Syntax_Syntax.vars = uu____12764;_},uu____12765))
                     ->
                     let uu____12806 = destruct_flex_t t1  in
                     let uu____12807 = destruct_flex_t t2  in
                     solve_t_flex_flex env orig wl uu____12806 uu____12807
                 | (FStar_Syntax_Syntax.Tm_uvar uu____12808,uu____12809) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____12810 = destruct_flex_t t1  in
                     solve_t_flex_rigid_eq env orig wl uu____12810 t2
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12811;
                       FStar_Syntax_Syntax.pos = uu____12812;
                       FStar_Syntax_Syntax.vars = uu____12813;_},uu____12814),uu____12815)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____12836 = destruct_flex_t t1  in
                     solve_t_flex_rigid_eq env orig wl uu____12836 t2
                 | (uu____12837,FStar_Syntax_Syntax.Tm_uvar uu____12838) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____12839,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12840;
                       FStar_Syntax_Syntax.pos = uu____12841;
                       FStar_Syntax_Syntax.vars = uu____12842;_},uu____12843))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____12864,FStar_Syntax_Syntax.Tm_type uu____12865) ->
                     solve_t' env
                       (let uu___151_12867 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___151_12867.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___151_12867.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___151_12867.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___151_12867.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___151_12867.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___151_12867.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___151_12867.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___151_12867.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___151_12867.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___151_12867.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12868;
                       FStar_Syntax_Syntax.pos = uu____12869;
                       FStar_Syntax_Syntax.vars = uu____12870;_},uu____12871),FStar_Syntax_Syntax.Tm_type
                    uu____12872) ->
                     solve_t' env
                       (let uu___151_12894 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___151_12894.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___151_12894.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___151_12894.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___151_12894.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___151_12894.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___151_12894.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___151_12894.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___151_12894.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___151_12894.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___151_12894.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____12895,FStar_Syntax_Syntax.Tm_arrow uu____12896) ->
                     solve_t' env
                       (let uu___151_12910 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___151_12910.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___151_12910.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___151_12910.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___151_12910.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___151_12910.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___151_12910.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___151_12910.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___151_12910.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___151_12910.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___151_12910.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12911;
                       FStar_Syntax_Syntax.pos = uu____12912;
                       FStar_Syntax_Syntax.vars = uu____12913;_},uu____12914),FStar_Syntax_Syntax.Tm_arrow
                    uu____12915) ->
                     solve_t' env
                       (let uu___151_12949 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___151_12949.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___151_12949.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___151_12949.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___151_12949.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___151_12949.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___151_12949.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___151_12949.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___151_12949.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___151_12949.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___151_12949.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____12950,uu____12951) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____12954 =
                          let uu____12955 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____12955
                           in
                        if uu____12954
                        then
                          let uu____12956 =
                            FStar_All.pipe_left
                              (fun _0_26  ->
                                 FStar_TypeChecker_Common.TProb _0_26)
                              (let uu___152_12960 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___152_12960.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___152_12960.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___152_12960.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___152_12960.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___152_12960.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___152_12960.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___152_12960.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___152_12960.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___152_12960.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___152_12960.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____12961 = destruct_flex_t t1  in
                          solve_t_flex_rigid_eq env uu____12956 wl
                            uu____12961 t2
                        else
                          (let uu____12963 = base_and_refinement env t2  in
                           match uu____12963 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12992 =
                                      FStar_All.pipe_left
                                        (fun _0_27  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_27)
                                        (let uu___153_12996 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___153_12996.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___153_12996.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___153_12996.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___153_12996.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___153_12996.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.logical_guard_uvar
                                             =
                                             (uu___153_12996.FStar_TypeChecker_Common.logical_guard_uvar);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___153_12996.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___153_12996.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___153_12996.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___153_12996.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____12997 = destruct_flex_t t1  in
                                    solve_t_flex_rigid_eq env uu____12992 wl
                                      uu____12997 t_base
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___154_13005 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___154_13005.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___154_13005.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let uu____13007 =
                                      mk_t_problem wl
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    (match uu____13007 with
                                     | (base_prob,wl1) ->
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         let wl2 =
                                           solve_prob orig
                                             (FStar_Pervasives_Native.Some
                                                guard) [] wl1
                                            in
                                         solve env (attempt [base_prob] wl2)))))
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____13018;
                       FStar_Syntax_Syntax.pos = uu____13019;
                       FStar_Syntax_Syntax.vars = uu____13020;_},uu____13021),uu____13022)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____13045 =
                          let uu____13046 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____13046
                           in
                        if uu____13045
                        then
                          let uu____13047 =
                            FStar_All.pipe_left
                              (fun _0_28  ->
                                 FStar_TypeChecker_Common.TProb _0_28)
                              (let uu___152_13051 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___152_13051.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___152_13051.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___152_13051.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___152_13051.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___152_13051.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___152_13051.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___152_13051.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___152_13051.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___152_13051.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___152_13051.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____13052 = destruct_flex_t t1  in
                          solve_t_flex_rigid_eq env uu____13047 wl
                            uu____13052 t2
                        else
                          (let uu____13054 = base_and_refinement env t2  in
                           match uu____13054 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____13083 =
                                      FStar_All.pipe_left
                                        (fun _0_29  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_29)
                                        (let uu___153_13087 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___153_13087.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___153_13087.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___153_13087.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___153_13087.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___153_13087.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.logical_guard_uvar
                                             =
                                             (uu___153_13087.FStar_TypeChecker_Common.logical_guard_uvar);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___153_13087.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___153_13087.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___153_13087.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___153_13087.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____13088 = destruct_flex_t t1  in
                                    solve_t_flex_rigid_eq env uu____13083 wl
                                      uu____13088 t_base
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___154_13096 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___154_13096.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___154_13096.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let uu____13098 =
                                      mk_t_problem wl
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    (match uu____13098 with
                                     | (base_prob,wl1) ->
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         let wl2 =
                                           solve_prob orig
                                             (FStar_Pervasives_Native.Some
                                                guard) [] wl1
                                            in
                                         solve env (attempt [base_prob] wl2)))))
                 | (uu____13109,FStar_Syntax_Syntax.Tm_uvar uu____13110) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____13112 = base_and_refinement env t1  in
                        match uu____13112 with
                        | (t_base,uu____13124) ->
                            solve_t env
                              (let uu___155_13138 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___155_13138.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___155_13138.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___155_13138.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___155_13138.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___155_13138.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___155_13138.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___155_13138.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___155_13138.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___155_13138.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____13139,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____13140;
                       FStar_Syntax_Syntax.pos = uu____13141;
                       FStar_Syntax_Syntax.vars = uu____13142;_},uu____13143))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____13165 = base_and_refinement env t1  in
                        match uu____13165 with
                        | (t_base,uu____13177) ->
                            solve_t env
                              (let uu___155_13191 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___155_13191.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___155_13191.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___155_13191.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___155_13191.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___155_13191.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___155_13191.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___155_13191.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___155_13191.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___155_13191.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____13192,uu____13193) ->
                     let t21 =
                       let uu____13201 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____13201  in
                     solve_t env
                       (let uu___156_13227 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___156_13227.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___156_13227.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___156_13227.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___156_13227.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___156_13227.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___156_13227.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___156_13227.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___156_13227.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___156_13227.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___156_13227.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____13228,FStar_Syntax_Syntax.Tm_refine uu____13229) ->
                     let t11 =
                       let uu____13237 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____13237  in
                     solve_t env
                       (let uu___157_13263 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_13263.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___157_13263.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_13263.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_13263.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_13263.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___157_13263.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_13263.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_13263.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_13263.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_13263.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                     let uu____13340 =
                       let uu____13345 = p_scope orig  in
                       mk_t_problem wl uu____13345 orig t11
                         FStar_TypeChecker_Common.EQ t21
                         FStar_Pervasives_Native.None "match scrutinee"
                        in
                     (match uu____13340 with
                      | (sc_prob,wl1) ->
                          let rec solve_branches wl2 brs11 brs21 =
                            match (brs11, brs21) with
                            | (br1::rs1,br2::rs2) ->
                                let uu____13558 = br1  in
                                (match uu____13558 with
                                 | (p1,w1,uu____13583) ->
                                     let uu____13600 = br2  in
                                     (match uu____13600 with
                                      | (p2,w2,uu____13619) ->
                                          let uu____13624 =
                                            let uu____13625 =
                                              FStar_Syntax_Syntax.eq_pat p1
                                                p2
                                               in
                                            Prims.op_Negation uu____13625  in
                                          if uu____13624
                                          then FStar_Pervasives_Native.None
                                          else
                                            (let uu____13641 =
                                               FStar_Syntax_Subst.open_branch'
                                                 br1
                                                in
                                             match uu____13641 with
                                             | ((p11,w11,e1),s) ->
                                                 let uu____13674 = br2  in
                                                 (match uu____13674 with
                                                  | (p21,w21,e2) ->
                                                      let w22 =
                                                        FStar_Util.map_opt
                                                          w21
                                                          (FStar_Syntax_Subst.subst
                                                             s)
                                                         in
                                                      let e21 =
                                                        FStar_Syntax_Subst.subst
                                                          s e2
                                                         in
                                                      let scope =
                                                        let uu____13709 =
                                                          p_scope orig  in
                                                        let uu____13716 =
                                                          let uu____13723 =
                                                            FStar_Syntax_Syntax.pat_bvs
                                                              p11
                                                             in
                                                          FStar_All.pipe_left
                                                            (FStar_List.map
                                                               FStar_Syntax_Syntax.mk_binder)
                                                            uu____13723
                                                           in
                                                        FStar_List.append
                                                          uu____13709
                                                          uu____13716
                                                         in
                                                      let uu____13738 =
                                                        match (w11, w22) with
                                                        | (FStar_Pervasives_Native.Some
                                                           uu____13759,FStar_Pervasives_Native.None
                                                           ) ->
                                                            FStar_Pervasives_Native.None
                                                        | (FStar_Pervasives_Native.None
                                                           ,FStar_Pervasives_Native.Some
                                                           uu____13770) ->
                                                            FStar_Pervasives_Native.None
                                                        | (FStar_Pervasives_Native.None
                                                           ,FStar_Pervasives_Native.None
                                                           ) ->
                                                            FStar_Pervasives_Native.Some
                                                              ([], wl2)
                                                        | (FStar_Pervasives_Native.Some
                                                           w12,FStar_Pervasives_Native.Some
                                                           w23) ->
                                                            let uu____13799 =
                                                              mk_t_problem
                                                                wl2 scope
                                                                orig w12
                                                                FStar_TypeChecker_Common.EQ
                                                                w23
                                                                FStar_Pervasives_Native.None
                                                                "when clause"
                                                               in
                                                            (match uu____13799
                                                             with
                                                             | (p,wl3) ->
                                                                 FStar_Pervasives_Native.Some
                                                                   ([p], wl3))
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____13738
                                                        (fun uu____13841  ->
                                                           match uu____13841
                                                           with
                                                           | (wprobs,wl3) ->
                                                               let uu____13862
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 scope
                                                                   orig e1
                                                                   FStar_TypeChecker_Common.EQ
                                                                   e21
                                                                   FStar_Pervasives_Native.None
                                                                   "branch body"
                                                                  in
                                                               (match uu____13862
                                                                with
                                                                | (prob,wl4)
                                                                    ->
                                                                    let uu____13877
                                                                    =
                                                                    solve_branches
                                                                    wl4 rs1
                                                                    rs2  in
                                                                    FStar_Util.bind_opt
                                                                    uu____13877
                                                                    (fun
                                                                    uu____13901
                                                                     ->
                                                                    match uu____13901
                                                                    with
                                                                    | 
                                                                    (r1,wl5)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl5))))))))
                            | ([],[]) ->
                                FStar_Pervasives_Native.Some ([], wl2)
                            | uu____13986 -> FStar_Pervasives_Native.None  in
                          let uu____14023 = solve_branches wl1 brs1 brs2  in
                          (match uu____14023 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env "Tm_match branches don't match"
                                 orig
                           | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                               let sub_probs1 = sc_prob :: sub_probs  in
                               let wl3 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl2
                                  in
                               solve env (attempt sub_probs1 wl3)))
                 | (FStar_Syntax_Syntax.Tm_match uu____14054,uu____14055) ->
                     let head1 =
                       let uu____14079 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14079
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14119 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14119
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14159 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14159
                       then
                         let uu____14160 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14161 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14162 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14160 uu____14161 uu____14162
                       else ());
                      (let uu____14164 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14164
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14171 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14171
                          then
                            let uu____14172 =
                              let uu____14179 =
                                let uu____14180 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14180 = FStar_Syntax_Util.Equal  in
                              if uu____14179
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14190 = mk_eq2 wl orig t1 t2  in
                                 match uu____14190 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14172 with
                            | (guard,wl1) ->
                                let uu____14211 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14211
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____14214,uu____14215) ->
                     let head1 =
                       let uu____14223 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14223
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14263 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14263
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14303 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14303
                       then
                         let uu____14304 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14305 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14306 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14304 uu____14305 uu____14306
                       else ());
                      (let uu____14308 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14308
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14315 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14315
                          then
                            let uu____14316 =
                              let uu____14323 =
                                let uu____14324 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14324 = FStar_Syntax_Util.Equal  in
                              if uu____14323
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14334 = mk_eq2 wl orig t1 t2  in
                                 match uu____14334 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14316 with
                            | (guard,wl1) ->
                                let uu____14355 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14355
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____14358,uu____14359) ->
                     let head1 =
                       let uu____14361 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14361
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14401 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14401
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14441 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14441
                       then
                         let uu____14442 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14443 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14444 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14442 uu____14443 uu____14444
                       else ());
                      (let uu____14446 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14446
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14453 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14453
                          then
                            let uu____14454 =
                              let uu____14461 =
                                let uu____14462 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14462 = FStar_Syntax_Util.Equal  in
                              if uu____14461
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14472 = mk_eq2 wl orig t1 t2  in
                                 match uu____14472 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14454 with
                            | (guard,wl1) ->
                                let uu____14493 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14493
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____14496,uu____14497)
                     ->
                     let head1 =
                       let uu____14499 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14499
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14539 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14539
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14579 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14579
                       then
                         let uu____14580 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14581 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14582 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14580 uu____14581 uu____14582
                       else ());
                      (let uu____14584 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14584
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14591 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14591
                          then
                            let uu____14592 =
                              let uu____14599 =
                                let uu____14600 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14600 = FStar_Syntax_Util.Equal  in
                              if uu____14599
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14610 = mk_eq2 wl orig t1 t2  in
                                 match uu____14610 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14592 with
                            | (guard,wl1) ->
                                let uu____14631 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14631
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____14634,uu____14635) ->
                     let head1 =
                       let uu____14637 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14637
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14677 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14677
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14717 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14717
                       then
                         let uu____14718 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14719 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14720 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14718 uu____14719 uu____14720
                       else ());
                      (let uu____14722 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14722
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14729 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14729
                          then
                            let uu____14730 =
                              let uu____14737 =
                                let uu____14738 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14738 = FStar_Syntax_Util.Equal  in
                              if uu____14737
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14748 = mk_eq2 wl orig t1 t2  in
                                 match uu____14748 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14730 with
                            | (guard,wl1) ->
                                let uu____14769 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14769
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____14772,uu____14773) ->
                     let head1 =
                       let uu____14789 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14789
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14829 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14829
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____14869 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____14869
                       then
                         let uu____14870 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____14871 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14872 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____14870 uu____14871 uu____14872
                       else ());
                      (let uu____14874 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14874
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____14881 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____14881
                          then
                            let uu____14882 =
                              let uu____14889 =
                                let uu____14890 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____14890 = FStar_Syntax_Util.Equal  in
                              if uu____14889
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____14900 = mk_eq2 wl orig t1 t2  in
                                 match uu____14900 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____14882 with
                            | (guard,wl1) ->
                                let uu____14921 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____14921
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____14924,FStar_Syntax_Syntax.Tm_match uu____14925) ->
                     let head1 =
                       let uu____14949 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____14949
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____14989 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____14989
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15029 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15029
                       then
                         let uu____15030 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15031 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15032 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15030 uu____15031 uu____15032
                       else ());
                      (let uu____15034 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15034
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15041 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15041
                          then
                            let uu____15042 =
                              let uu____15049 =
                                let uu____15050 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15050 = FStar_Syntax_Util.Equal  in
                              if uu____15049
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15060 = mk_eq2 wl orig t1 t2  in
                                 match uu____15060 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15042 with
                            | (guard,wl1) ->
                                let uu____15081 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15081
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____15084,FStar_Syntax_Syntax.Tm_uinst uu____15085) ->
                     let head1 =
                       let uu____15093 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____15093
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____15133 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____15133
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15173 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15173
                       then
                         let uu____15174 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15175 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15176 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15174 uu____15175 uu____15176
                       else ());
                      (let uu____15178 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15178
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15185 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15185
                          then
                            let uu____15186 =
                              let uu____15193 =
                                let uu____15194 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15194 = FStar_Syntax_Util.Equal  in
                              if uu____15193
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15204 = mk_eq2 wl orig t1 t2  in
                                 match uu____15204 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15186 with
                            | (guard,wl1) ->
                                let uu____15225 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15225
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____15228,FStar_Syntax_Syntax.Tm_name uu____15229) ->
                     let head1 =
                       let uu____15231 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____15231
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____15271 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____15271
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15311 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15311
                       then
                         let uu____15312 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15313 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15314 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15312 uu____15313 uu____15314
                       else ());
                      (let uu____15316 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15316
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15323 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15323
                          then
                            let uu____15324 =
                              let uu____15331 =
                                let uu____15332 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15332 = FStar_Syntax_Util.Equal  in
                              if uu____15331
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15342 = mk_eq2 wl orig t1 t2  in
                                 match uu____15342 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15324 with
                            | (guard,wl1) ->
                                let uu____15363 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15363
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____15366,FStar_Syntax_Syntax.Tm_constant uu____15367)
                     ->
                     let head1 =
                       let uu____15369 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____15369
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____15409 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____15409
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15449 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15449
                       then
                         let uu____15450 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15451 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15452 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15450 uu____15451 uu____15452
                       else ());
                      (let uu____15454 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15454
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15461 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15461
                          then
                            let uu____15462 =
                              let uu____15469 =
                                let uu____15470 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15470 = FStar_Syntax_Util.Equal  in
                              if uu____15469
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15480 = mk_eq2 wl orig t1 t2  in
                                 match uu____15480 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15462 with
                            | (guard,wl1) ->
                                let uu____15501 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15501
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____15504,FStar_Syntax_Syntax.Tm_fvar uu____15505) ->
                     let head1 =
                       let uu____15507 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____15507
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____15547 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____15547
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15587 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15587
                       then
                         let uu____15588 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15589 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15590 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15588 uu____15589 uu____15590
                       else ());
                      (let uu____15592 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15592
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15599 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15599
                          then
                            let uu____15600 =
                              let uu____15607 =
                                let uu____15608 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15608 = FStar_Syntax_Util.Equal  in
                              if uu____15607
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15618 = mk_eq2 wl orig t1 t2  in
                                 match uu____15618 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15600 with
                            | (guard,wl1) ->
                                let uu____15639 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15639
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____15642,FStar_Syntax_Syntax.Tm_app uu____15643) ->
                     let head1 =
                       let uu____15659 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____15659
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____15699 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____15699
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____15739 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____15739
                       then
                         let uu____15740 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____15741 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15742 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____15740 uu____15741 uu____15742
                       else ());
                      (let uu____15744 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15744
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____15751 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____15751
                          then
                            let uu____15752 =
                              let uu____15759 =
                                let uu____15760 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____15760 = FStar_Syntax_Util.Equal  in
                              if uu____15759
                              then (FStar_Pervasives_Native.None, wl)
                              else
                                (let uu____15770 = mk_eq2 wl orig t1 t2  in
                                 match uu____15770 with
                                 | (g,wl1) ->
                                     ((FStar_Pervasives_Native.Some g), wl1))
                               in
                            match uu____15752 with
                            | (guard,wl1) ->
                                let uu____15791 =
                                  solve_prob orig guard [] wl1  in
                                solve env uu____15791
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____15794,FStar_Syntax_Syntax.Tm_let uu____15795) ->
                     let uu____15820 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____15820
                     then
                       let uu____15821 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____15821
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____15823,uu____15824) ->
                     let uu____15837 =
                       let uu____15842 =
                         let uu____15843 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____15844 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____15845 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____15846 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____15843 uu____15844 uu____15845 uu____15846
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____15842)
                        in
                     FStar_Errors.raise_error uu____15837
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____15847,FStar_Syntax_Syntax.Tm_let uu____15848) ->
                     let uu____15861 =
                       let uu____15866 =
                         let uu____15867 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____15868 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____15869 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____15870 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____15867 uu____15868 uu____15869 uu____15870
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____15866)
                        in
                     FStar_Errors.raise_error uu____15861
                       t1.FStar_Syntax_Syntax.pos
                 | uu____15871 -> giveup env "head tag mismatch" orig)))))

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
          let uu____15914 = p_scope orig  in
          mk_t_problem wl1 uu____15914 orig t1 rel t2
            FStar_Pervasives_Native.None reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____15927 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____15927
           then
             let uu____15928 =
               let uu____15929 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____15929  in
             let uu____15930 =
               let uu____15931 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____15931  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____15928 uu____15930
           else ());
          (let uu____15933 =
             let uu____15934 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____15934  in
           if uu____15933
           then
             let uu____15935 =
               let uu____15936 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____15937 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____15936 uu____15937
                in
             giveup env uu____15935 orig
           else
             (let uu____15939 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____15939 with
              | (ret_sub_prob,wl1) ->
                  let uu____15946 =
                    FStar_List.fold_right2
                      (fun uu____15979  ->
                         fun uu____15980  ->
                           fun uu____15981  ->
                             match (uu____15979, uu____15980, uu____15981)
                             with
                             | ((a1,uu____16017),(a2,uu____16019),(arg_sub_probs,wl2))
                                 ->
                                 let uu____16040 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____16040 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____15946 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____16067 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____16067  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____16093 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____16096)::[] -> wp1
              | uu____16113 ->
                  let uu____16122 =
                    let uu____16123 =
                      let uu____16124 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____16124  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____16123
                     in
                  failwith uu____16122
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____16126 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____16126]
              | x -> x  in
            let uu____16128 =
              let uu____16137 =
                let uu____16144 =
                  let uu____16145 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____16145 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____16144  in
              [uu____16137]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____16128;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____16158 = lift_c1 ()  in solve_eq uu____16158 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___109_16164  ->
                       match uu___109_16164 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____16165 -> false))
                in
             let uu____16166 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____16192)::uu____16193,(wp2,uu____16195)::uu____16196)
                   -> (wp1, wp2)
               | uu____16253 ->
                   let uu____16274 =
                     let uu____16279 =
                       let uu____16280 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____16281 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____16280 uu____16281
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____16279)
                      in
                   FStar_Errors.raise_error uu____16274
                     env.FStar_TypeChecker_Env.range
                in
             match uu____16166 with
             | (wpc1,wpc2) ->
                 let uu____16288 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____16288
                 then
                   let uu____16289 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____16289 wl
                 else
                   (let uu____16291 =
                      let uu____16298 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____16298  in
                    match uu____16291 with
                    | (c2_decl,qualifiers) ->
                        let uu____16319 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____16319
                        then
                          let c1_repr =
                            let uu____16323 =
                              let uu____16324 =
                                let uu____16325 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____16325  in
                              let uu____16326 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____16324 uu____16326
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____16323
                             in
                          let c2_repr =
                            let uu____16328 =
                              let uu____16329 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____16330 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____16329 uu____16330
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____16328
                             in
                          let uu____16331 =
                            let uu____16336 =
                              let uu____16337 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____16338 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____16337 uu____16338
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____16336
                             in
                          (match uu____16331 with
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
                                 ((let uu____16346 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____16346
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____16349 =
                                     let uu____16356 =
                                       let uu____16357 =
                                         let uu____16372 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____16375 =
                                           let uu____16384 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____16385 =
                                             let uu____16388 =
                                               let uu____16389 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____16389
                                                in
                                             [uu____16388]  in
                                           uu____16384 :: uu____16385  in
                                         (uu____16372, uu____16375)  in
                                       FStar_Syntax_Syntax.Tm_app uu____16357
                                        in
                                     FStar_Syntax_Syntax.mk uu____16356  in
                                   uu____16349 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____16406 =
                                    let uu____16413 =
                                      let uu____16414 =
                                        let uu____16429 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____16432 =
                                          let uu____16441 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____16442 =
                                            let uu____16445 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____16446 =
                                              let uu____16449 =
                                                let uu____16450 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____16450
                                                 in
                                              [uu____16449]  in
                                            uu____16445 :: uu____16446  in
                                          uu____16441 :: uu____16442  in
                                        (uu____16429, uu____16432)  in
                                      FStar_Syntax_Syntax.Tm_app uu____16414
                                       in
                                    FStar_Syntax_Syntax.mk uu____16413  in
                                  uu____16406 FStar_Pervasives_Native.None r)
                              in
                           let uu____16464 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____16464 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____16472 =
                                   let uu____16475 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_30  ->
                                        FStar_Pervasives_Native.Some _0_30)
                                     uu____16475
                                    in
                                 solve_prob orig uu____16472 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____16478 = FStar_Util.physical_equality c1 c2  in
        if uu____16478
        then
          let uu____16479 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____16479
        else
          ((let uu____16482 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____16482
            then
              let uu____16483 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____16484 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____16483
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____16484
            else ());
           (let uu____16486 =
              let uu____16495 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____16498 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____16495, uu____16498)  in
            match uu____16486 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____16516),FStar_Syntax_Syntax.Total
                    (t2,uu____16518)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____16535 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____16535 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____16536,FStar_Syntax_Syntax.Total uu____16537) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____16555),FStar_Syntax_Syntax.Total
                    (t2,uu____16557)) ->
                     let uu____16574 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____16574 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____16576),FStar_Syntax_Syntax.GTotal
                    (t2,uu____16578)) ->
                     let uu____16595 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____16595 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____16597),FStar_Syntax_Syntax.GTotal
                    (t2,uu____16599)) ->
                     let uu____16616 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____16616 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____16617,FStar_Syntax_Syntax.Comp uu____16618) ->
                     let uu____16627 =
                       let uu___158_16630 = problem  in
                       let uu____16633 =
                         let uu____16634 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____16634
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_16630.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____16633;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_16630.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_16630.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_16630.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_16630.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___158_16630.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_16630.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_16630.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_16630.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_16630.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____16627 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____16635,FStar_Syntax_Syntax.Comp uu____16636) ->
                     let uu____16645 =
                       let uu___158_16648 = problem  in
                       let uu____16651 =
                         let uu____16652 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____16652
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_16648.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____16651;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_16648.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_16648.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_16648.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_16648.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___158_16648.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_16648.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_16648.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_16648.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_16648.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____16645 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____16653,FStar_Syntax_Syntax.GTotal uu____16654) ->
                     let uu____16663 =
                       let uu___159_16666 = problem  in
                       let uu____16669 =
                         let uu____16670 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____16670
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_16666.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_16666.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_16666.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____16669;
                         FStar_TypeChecker_Common.element =
                           (uu___159_16666.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_16666.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___159_16666.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_16666.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_16666.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_16666.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_16666.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____16663 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____16671,FStar_Syntax_Syntax.Total uu____16672) ->
                     let uu____16681 =
                       let uu___159_16684 = problem  in
                       let uu____16687 =
                         let uu____16688 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____16688
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_16684.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_16684.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_16684.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____16687;
                         FStar_TypeChecker_Common.element =
                           (uu___159_16684.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_16684.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___159_16684.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_16684.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_16684.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_16684.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_16684.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____16681 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____16689,FStar_Syntax_Syntax.Comp uu____16690) ->
                     let uu____16691 =
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
                     if uu____16691
                     then
                       let uu____16692 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____16692 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____16696 =
                            let uu____16701 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____16701
                            then (c1_comp, c2_comp)
                            else
                              (let uu____16707 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____16708 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____16707, uu____16708))
                             in
                          match uu____16696 with
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
                           (let uu____16715 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16715
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____16717 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____16717 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____16720 =
                                  let uu____16721 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____16722 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____16721 uu____16722
                                   in
                                giveup env uu____16720 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____16729 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____16762  ->
              match uu____16762 with
              | (uu____16773,tm,uu____16775,uu____16776,uu____16777) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____16729 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____16810 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____16810 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____16828 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____16856  ->
                match uu____16856 with
                | (u1,u2) ->
                    let uu____16863 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____16864 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____16863 uu____16864))
         in
      FStar_All.pipe_right uu____16828 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____16891,[])) -> "{}"
      | uu____16916 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____16939 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____16939
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____16942 =
              FStar_List.map
                (fun uu____16952  ->
                   match uu____16952 with
                   | (uu____16957,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____16942 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____16962 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____16962 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
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
                  let uu____17007 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____17007
                  then
                    let uu____17008 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____17009 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____17008
                      (rel_to_string rel) uu____17009
                  else "TOP"  in
                let uu____17011 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____17011 with
                | (p,wl1) -> ((FStar_TypeChecker_Common.TProb p), wl1)
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv,worklist)
              FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____17060 =
                let uu____17063 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                  uu____17063
                 in
              FStar_Syntax_Syntax.new_bv uu____17060 t1  in
            let uu____17066 =
              let uu____17071 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____17071
               in
            match uu____17066 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____17127 = FStar_Options.eager_inference ()  in
          if uu____17127
          then
            let uu___160_17128 = probs  in
            {
              attempting = (uu___160_17128.attempting);
              wl_deferred = (uu___160_17128.wl_deferred);
              ctr = (uu___160_17128.ctr);
              defer_ok = false;
              smt_ok = (uu___160_17128.smt_ok);
              tcenv = (uu___160_17128.tcenv);
              wl_implicits = (uu___160_17128.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____17148 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____17148
              then
                let uu____17149 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____17149
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
          ((let uu____17171 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____17171
            then
              let uu____17172 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____17172
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____17176 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____17176
             then
               let uu____17177 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____17177
             else ());
            (let f2 =
               let uu____17180 =
                 let uu____17181 = FStar_Syntax_Util.unmeta f1  in
                 uu____17181.FStar_Syntax_Syntax.n  in
               match uu____17180 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____17185 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___161_17186 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___161_17186.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___161_17186.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___161_17186.FStar_TypeChecker_Env.implicits)
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
            let uu____17300 =
              let uu____17301 =
                let uu____17302 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____17302;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____17301  in
            FStar_All.pipe_left
              (fun _0_33  -> FStar_Pervasives_Native.Some _0_33) uu____17300
  
let with_guard_no_simp :
  'Auu____17317 .
    'Auu____17317 ->
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
            let uu____17340 =
              let uu____17341 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____17341;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____17340
  
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
          (let uu____17381 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____17381
           then
             let uu____17382 = FStar_Syntax_Print.term_to_string t1  in
             let uu____17383 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____17382
               uu____17383
           else ());
          (let uu____17385 =
             let uu____17390 = empty_worklist env  in
             let uu____17391 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____17390 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____17391
              in
           match uu____17385 with
           | (prob,wl) ->
               let g =
                 let uu____17399 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____17419  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____17399  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____17463 = try_teq true env t1 t2  in
        match uu____17463 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____17467 = FStar_TypeChecker_Env.get_range env  in
              let uu____17468 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____17467 uu____17468);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____17475 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____17475
              then
                let uu____17476 = FStar_Syntax_Print.term_to_string t1  in
                let uu____17477 = FStar_Syntax_Print.term_to_string t2  in
                let uu____17478 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____17476
                  uu____17477 uu____17478
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
          let uu____17500 = FStar_TypeChecker_Env.get_range env  in
          let uu____17501 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____17500 uu____17501
  
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
        (let uu____17526 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____17526
         then
           let uu____17527 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____17528 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____17527 uu____17528
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____17531 =
           let uu____17538 = empty_worklist env  in
           let uu____17539 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____17538 env c1 rel c2 FStar_Pervasives_Native.None
             uu____17539 "sub_comp"
            in
         match uu____17531 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____17549 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____17569  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____17549)
  
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
      fun uu____17624  ->
        match uu____17624 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____17667 =
                 let uu____17672 =
                   let uu____17673 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____17674 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____17673 uu____17674
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____17672)  in
               let uu____17675 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____17667 uu____17675)
               in
            let equiv1 v1 v' =
              let uu____17687 =
                let uu____17692 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____17693 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____17692, uu____17693)  in
              match uu____17687 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____17712 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____17742 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____17742 with
                      | FStar_Syntax_Syntax.U_unif uu____17749 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____17778  ->
                                    match uu____17778 with
                                    | (u,v') ->
                                        let uu____17787 = equiv1 v1 v'  in
                                        if uu____17787
                                        then
                                          let uu____17790 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____17790 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____17806 -> []))
               in
            let uu____17811 =
              let wl =
                let uu___162_17815 = empty_worklist env  in
                {
                  attempting = (uu___162_17815.attempting);
                  wl_deferred = (uu___162_17815.wl_deferred);
                  ctr = (uu___162_17815.ctr);
                  defer_ok = false;
                  smt_ok = (uu___162_17815.smt_ok);
                  tcenv = (uu___162_17815.tcenv);
                  wl_implicits = (uu___162_17815.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____17833  ->
                      match uu____17833 with
                      | (lb,v1) ->
                          let uu____17840 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____17840 with
                           | USolved wl1 -> ()
                           | uu____17842 -> fail1 lb v1)))
               in
            let rec check_ineq uu____17852 =
              match uu____17852 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____17861) -> true
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
                      uu____17884,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____17886,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____17897) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____17904,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____17912 -> false)
               in
            let uu____17917 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____17932  ->
                      match uu____17932 with
                      | (u,v1) ->
                          let uu____17939 = check_ineq (u, v1)  in
                          if uu____17939
                          then true
                          else
                            ((let uu____17942 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____17942
                              then
                                let uu____17943 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____17944 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____17943
                                  uu____17944
                              else ());
                             false)))
               in
            if uu____17917
            then ()
            else
              ((let uu____17948 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____17948
                then
                  ((let uu____17950 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____17950);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____17960 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____17960))
                else ());
               (let uu____17970 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____17970))
  
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
        let fail1 uu____18037 =
          match uu____18037 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___163_18058 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___163_18058.attempting);
            wl_deferred = (uu___163_18058.wl_deferred);
            ctr = (uu___163_18058.ctr);
            defer_ok;
            smt_ok = (uu___163_18058.smt_ok);
            tcenv = (uu___163_18058.tcenv);
            wl_implicits = (uu___163_18058.wl_implicits)
          }  in
        (let uu____18060 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____18060
         then
           let uu____18061 = wl_to_string wl  in
           let uu____18062 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print2
             "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
             uu____18061 uu____18062
         else ());
        (let g1 =
           let uu____18075 = solve_and_commit env wl fail1  in
           match uu____18075 with
           | FStar_Pervasives_Native.Some
               (uu____18082::uu____18083,uu____18084) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___164_18109 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___164_18109.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___164_18109.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____18120 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___165_18128 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___165_18128.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___165_18128.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___165_18128.FStar_TypeChecker_Env.implicits)
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
    let uu____18176 = FStar_ST.op_Bang last_proof_ns  in
    match uu____18176 with
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
            let uu___166_18299 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___166_18299.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___166_18299.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___166_18299.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____18300 =
            let uu____18301 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____18301  in
          if uu____18300
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____18309 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____18310 =
                       let uu____18311 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____18311
                        in
                     FStar_Errors.diag uu____18309 uu____18310)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____18315 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____18316 =
                        let uu____18317 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____18317
                         in
                      FStar_Errors.diag uu____18315 uu____18316)
                   else ();
                   (let uu____18320 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____18320 "discharge_guard'"
                      env vc1);
                   (let uu____18321 = check_trivial vc1  in
                    match uu____18321 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____18328 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____18329 =
                                let uu____18330 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____18330
                                 in
                              FStar_Errors.diag uu____18328 uu____18329)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____18335 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____18336 =
                                let uu____18337 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____18337
                                 in
                              FStar_Errors.diag uu____18335 uu____18336)
                           else ();
                           (let vcs =
                              let uu____18348 = FStar_Options.use_tactics ()
                                 in
                              if uu____18348
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____18367  ->
                                     (let uu____18369 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____18369);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____18371 =
                                   let uu____18378 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____18378)  in
                                 [uu____18371])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____18412  ->
                                    match uu____18412 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____18423 = check_trivial goal1
                                           in
                                        (match uu____18423 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal2 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____18431 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____18432 =
                                                   let uu____18433 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____18434 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____18433 uu____18434
                                                    in
                                                 FStar_Errors.diag
                                                   uu____18431 uu____18432)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____18437 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____18438 =
                                                   let uu____18439 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____18439
                                                    in
                                                 FStar_Errors.diag
                                                   uu____18437 uu____18438)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____18453 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____18453 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____18460 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____18460
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____18471 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____18471 with
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
            let uu____18504 = FStar_Syntax_Util.head_and_args u  in
            match uu____18504 with
            | (hd1,uu____18520) ->
                let uu____18541 =
                  let uu____18542 = FStar_Syntax_Subst.compress u  in
                  uu____18542.FStar_Syntax_Syntax.n  in
                (match uu____18541 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____18545 -> true
                 | uu____18546 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____18566 = acc  in
            match uu____18566 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____18628 = hd1  in
                     (match uu____18628 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____18645 = unresolved tm  in
                             if uu____18645
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___167_18658 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___167_18658.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___167_18658.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___167_18658.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___167_18658.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___167_18658.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___167_18658.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___167_18658.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___167_18658.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___167_18658.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___167_18658.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___167_18658.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___167_18658.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___167_18658.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___167_18658.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___167_18658.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___167_18658.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___167_18658.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___167_18658.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___167_18658.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___167_18658.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___167_18658.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___167_18658.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___167_18658.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___167_18658.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___167_18658.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___167_18658.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___167_18658.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___167_18658.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___167_18658.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___167_18658.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___167_18658.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___167_18658.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___167_18658.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___167_18658.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___167_18658.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___167_18658.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___167_18658.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___168_18661 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___168_18661.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___168_18661.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___168_18661.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___168_18661.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___168_18661.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___168_18661.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___168_18661.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___168_18661.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___168_18661.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___168_18661.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___168_18661.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___168_18661.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___168_18661.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___168_18661.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___168_18661.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___168_18661.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___168_18661.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___168_18661.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___168_18661.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___168_18661.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___168_18661.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___168_18661.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___168_18661.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___168_18661.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___168_18661.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___168_18661.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___168_18661.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___168_18661.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___168_18661.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___168_18661.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___168_18661.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___168_18661.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___168_18661.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___168_18661.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___168_18661.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___168_18661.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___168_18661.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____18664 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____18664
                                 then
                                   let uu____18665 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____18666 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____18667 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____18668 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____18665 uu____18666 uu____18667
                                     reason uu____18668
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e ->
                                       ((let uu____18679 =
                                           let uu____18688 =
                                             let uu____18695 =
                                               let uu____18696 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____18697 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____18696 uu____18697
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____18695, r)
                                              in
                                           [uu____18688]  in
                                         FStar_Errors.add_errors uu____18679);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___171_18711 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___171_18711.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___171_18711.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___171_18711.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____18714 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____18721  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____18714 with
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
          let uu___172_18733 = g  in
          let uu____18734 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___172_18733.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___172_18733.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___172_18733.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____18734
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
        let uu____18788 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____18788 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____18799 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____18799
      | (reason,e,ctx_u,r,should_check)::uu____18805 ->
          let uu____18828 =
            let uu____18833 =
              let uu____18834 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____18835 =
                FStar_Syntax_Print.term_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____18836 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____18834 uu____18835 reason uu____18836
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____18833)
             in
          FStar_Errors.raise_error uu____18828 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___173_18847 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___173_18847.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___173_18847.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___173_18847.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____18870 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____18870 with
      | FStar_Pervasives_Native.Some uu____18876 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____18892 = try_teq false env t1 t2  in
        match uu____18892 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____18918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____18918
         then
           let uu____18919 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____18920 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____18919
             uu____18920
         else ());
        (let uu____18922 =
           let uu____18929 = empty_worklist env  in
           new_t_prob uu____18929 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____18922 with
         | (prob,x,wl) ->
             let g =
               let uu____18942 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____18962  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____18942  in
             ((let uu____18992 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____18992
               then
                 let uu____18993 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____18994 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____18995 =
                   let uu____18996 = FStar_Util.must g  in
                   guard_to_string env uu____18996  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____18993 uu____18994 uu____18995
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
        let uu____19030 = check_subtyping env t1 t2  in
        match uu____19030 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____19049 =
              let uu____19050 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____19050 g  in
            FStar_Pervasives_Native.Some uu____19049
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____19068 = check_subtyping env t1 t2  in
        match uu____19068 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____19087 =
              let uu____19088 =
                let uu____19089 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____19089]  in
              close_guard env uu____19088 g  in
            FStar_Pervasives_Native.Some uu____19087
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____19118 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____19118
         then
           let uu____19119 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____19120 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____19119
             uu____19120
         else ());
        (let uu____19122 =
           let uu____19129 = empty_worklist env  in
           new_t_prob uu____19129 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____19122 with
         | (prob,x,wl) ->
             let g =
               let uu____19136 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____19156  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____19136  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____19187 =
                      let uu____19188 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____19188]  in
                    close_guard env uu____19187 g1  in
                  discharge_guard_nosmt env g2))
  