open Prims
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
        FStar_TypeChecker_Env.univ_ineqs = uu____36;
        FStar_TypeChecker_Env.implicits = uu____37;_} -> true
    | uu____64 -> false
  
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
          let uu___142_101 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___142_101.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___142_101.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___142_101.FStar_TypeChecker_Env.implicits)
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
          let uu____136 = FStar_Options.defensive ()  in
          if uu____136
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____140 =
              let uu____141 =
                let uu____142 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____142  in
              Prims.op_Negation uu____141  in
            (if uu____140
             then
               let uu____147 =
                 let uu____152 =
                   let uu____153 = FStar_Syntax_Print.term_to_string t  in
                   let uu____154 =
                     let uu____155 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____155
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____153 uu____154
                    in
                 (FStar_Errors.Warning_Defensive, uu____152)  in
               FStar_Errors.log_issue rng uu____147
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____177 =
          let uu____178 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____178  in
        if uu____177
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
          let uu____204 =
            let uu____205 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____205  in
          if uu____204
          then ()
          else
            (let uu____207 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____207 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____230 =
            let uu____231 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____231  in
          if uu____230
          then ()
          else
            (let uu____233 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____233 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___143_247 = g  in
          let uu____248 =
            let uu____249 =
              let uu____250 =
                let uu____257 =
                  let uu____258 =
                    let uu____273 =
                      let uu____276 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____276]  in
                    (f, uu____273)  in
                  FStar_Syntax_Syntax.Tm_app uu____258  in
                FStar_Syntax_Syntax.mk uu____257  in
              uu____250 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
              uu____249
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____248;
            FStar_TypeChecker_Env.deferred =
              (uu___143_247.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___143_247.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___143_247.FStar_TypeChecker_Env.implicits)
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
          let uu___144_298 = g  in
          let uu____299 =
            let uu____300 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____300  in
          {
            FStar_TypeChecker_Env.guard_f = uu____299;
            FStar_TypeChecker_Env.deferred =
              (uu___144_298.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___144_298.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___144_298.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____306 -> failwith "impossible"
  
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
          let uu____321 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____321
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____327 =
      let uu____328 = FStar_Syntax_Util.unmeta t  in
      uu____328.FStar_Syntax_Syntax.n  in
    match uu____327 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____332 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____373 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____373;
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
                       let uu____454 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____454
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___145_456 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___145_456.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___145_456.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___145_456.FStar_TypeChecker_Env.implicits)
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
               let uu____481 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____481
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
            let uu___146_500 = g  in
            let uu____501 =
              let uu____502 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____502  in
            {
              FStar_TypeChecker_Env.guard_f = uu____501;
              FStar_TypeChecker_Env.deferred =
                (uu___146_500.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___146_500.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___146_500.FStar_TypeChecker_Env.implicits)
            }
  
let (new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh ()  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r
               in
            (uv1, uv1)
        | uu____538 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____563 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____563  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____571 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____571, uv1)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____622 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____664 -> false
  
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
  tcenv: FStar_TypeChecker_Env.env }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
  
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____872 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____890 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____915 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____921 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____927 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob = (FStar_Syntax_Syntax.comp,unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___112_952  ->
    match uu___112_952 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____960 =
        let uu____961 = FStar_Syntax_Subst.compress t  in
        uu____961.FStar_Syntax_Syntax.n  in
      match uu____960 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____990 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____991 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____990 uu____991
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____994;
             FStar_Syntax_Syntax.vars = uu____995;_},args)
          ->
          let uu____1041 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____1042 = FStar_Syntax_Print.term_to_string ty  in
          let uu____1043 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____1041 uu____1042 uu____1043
      | uu____1044 -> "--"  in
    let uu____1045 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____1045 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___113_1055  ->
      match uu___113_1055 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1061 =
            let uu____1064 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1065 =
              let uu____1068 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1069 =
                let uu____1072 =
                  let uu____1075 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1075]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1072
                 in
              uu____1068 :: uu____1069  in
            uu____1064 :: uu____1065  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1061
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1081 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1082 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1083 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1081 uu____1082
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1083
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___114_1093  ->
      match uu___114_1093 with
      | UNIV (u,t) ->
          let x =
            let uu____1097 = FStar_Options.hide_uvar_nums ()  in
            if uu____1097
            then "?"
            else
              (let uu____1099 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1099 FStar_Util.string_of_int)
             in
          let uu____1100 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1100
      | TERM ((u,uu____1102),t) ->
          let x =
            let uu____1109 = FStar_Options.hide_uvar_nums ()  in
            if uu____1109
            then "?"
            else
              (let uu____1111 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____1111 FStar_Util.string_of_int)
             in
          let uu____1112 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1112
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1127 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1127 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1141 =
      let uu____1144 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1144
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1141 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1157 .
    (FStar_Syntax_Syntax.term,'Auu____1157) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1175 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1193  ->
              match uu____1193 with
              | (x,uu____1199) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1175 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1207 =
      let uu____1208 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1208  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1207;
      smt_ok = true;
      tcenv = env
    }
  
let (singleton' :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist)
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___147_1230 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___147_1230.wl_deferred);
          ctr = (uu___147_1230.ctr);
          defer_ok = (uu___147_1230.defer_ok);
          smt_ok;
          tcenv = (uu___147_1230.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1247 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1247,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___148_1270 = empty_worklist env  in
      let uu____1271 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1271;
        wl_deferred = (uu___148_1270.wl_deferred);
        ctr = (uu___148_1270.ctr);
        defer_ok = false;
        smt_ok = (uu___148_1270.smt_ok);
        tcenv = (uu___148_1270.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___149_1291 = wl  in
        {
          attempting = (uu___149_1291.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___149_1291.ctr);
          defer_ok = (uu___149_1291.defer_ok);
          smt_ok = (uu___149_1291.smt_ok);
          tcenv = (uu___149_1291.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___150_1312 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___150_1312.wl_deferred);
        ctr = (uu___150_1312.ctr);
        defer_ok = (uu___150_1312.defer_ok);
        smt_ok = (uu___150_1312.smt_ok);
        tcenv = (uu___150_1312.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1329 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1329
         then
           let uu____1330 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1330
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___115_1336  ->
    match uu___115_1336 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1343 'Auu____1344 .
    ('Auu____1343,'Auu____1344) FStar_TypeChecker_Common.problem ->
      ('Auu____1343,'Auu____1344) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___151_1362 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___151_1362.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___151_1362.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___151_1362.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___151_1362.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___151_1362.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___151_1362.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___151_1362.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1373 'Auu____1374 .
    ('Auu____1373,'Auu____1374) FStar_TypeChecker_Common.problem ->
      ('Auu____1373,'Auu____1374) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___116_1397  ->
    match uu___116_1397 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___117_1425  ->
      match uu___117_1425 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___118_1430  ->
    match uu___118_1430 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___119_1445  ->
    match uu___119_1445 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___120_1462  ->
    match uu___120_1462 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___121_1479  ->
    match uu___121_1479 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___122_1498  ->
    match uu___122_1498 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let def_scope_wf :
  'Auu____1521 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1521) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1549 =
          let uu____1550 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1550  in
        if uu____1549
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1584)::bs ->
                 (def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)
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
        let uu____1629 =
          let uu____1630 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1630  in
        if uu____1629
        then ()
        else
          (let uu____1632 =
             let uu____1635 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1635
              in
           def_check_closed_in (p_loc prob) msg uu____1632 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1665 =
         let uu____1666 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1666  in
       if uu____1665
       then ()
       else
         (let uu____1668 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1668));
      (let uu____1676 =
         FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard") prob uu____1676);
      (let uu____1682 =
         FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1682);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1693 -> ())
  
let (mk_eq2 :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun prob  ->
    fun t1  ->
      fun t2  ->
        let uu____1714 = FStar_Syntax_Util.type_u ()  in
        match uu____1714 with
        | (t_type,u) ->
            let uu____1721 =
              let uu____1726 = p_scope prob  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____1726 t_type  in
            (match uu____1721 with
             | (tt,uu____1728) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___123_1733  ->
    match uu___123_1733 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1757 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1757 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1771  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1869 'Auu____1870 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1869 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1869 ->
              'Auu____1870 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1869,'Auu____1870)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1914 = next_pid ()  in
                let uu____1915 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1914;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1915;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1938 'Auu____1939 .
    FStar_TypeChecker_Env.env ->
      'Auu____1938 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1938 ->
            'Auu____1939 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1938,'Auu____1939)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env  in
                let uu____1984 = next_pid ()  in
                let uu____1985 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1984;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1985;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____2006 'Auu____2007 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2006 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2006 ->
            'Auu____2007 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____2006,'Auu____2007) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2046 = next_pid ()  in
              let uu____2047 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____2046;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____2047;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____2058 .
    worklist ->
      ('Auu____2058,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
        let uu____2118 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____2118
        then
          let uu____2119 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2120 = prob_to_string env d  in
          let uu____2121 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2119 uu____2120 uu____2121 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2127 -> failwith "impossible"  in
           let uu____2128 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2142 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2143 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2142, uu____2143)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2149 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2150 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2149, uu____2150)
              in
           match uu____2128 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___124_2168  ->
            match uu___124_2168 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2180 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____2182),t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar u t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___125_2207  ->
           match uu___125_2207 with
           | UNIV uu____2210 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____2216),t) ->
               let uu____2222 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____2222
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
        (fun uu___126_2246  ->
           match uu___126_2246 with
           | UNIV (u',t) ->
               let uu____2251 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2251
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2255 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2266 =
        let uu____2267 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2267
         in
      FStar_Syntax_Subst.compress uu____2266
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2278 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2278
  
let norm_arg :
  'Auu____2285 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2285) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2285)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2308 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2308, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2343  ->
              match uu____2343 with
              | (x,imp) ->
                  let uu____2354 =
                    let uu___152_2355 = x  in
                    let uu____2356 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___152_2355.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___152_2355.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2356
                    }  in
                  (uu____2354, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2377 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2377
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2381 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2381
        | uu____2384 -> u2  in
      let uu____2385 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2385
  
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
                (let uu____2511 = norm_refinement env t12  in
                 match uu____2511 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2528;
                     FStar_Syntax_Syntax.vars = uu____2529;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2555 =
                       let uu____2556 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2557 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2556 uu____2557
                        in
                     failwith uu____2555)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2573 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2573
          | FStar_Syntax_Syntax.Tm_uinst uu____2574 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2611 =
                   let uu____2612 = FStar_Syntax_Subst.compress t1'  in
                   uu____2612.FStar_Syntax_Syntax.n  in
                 match uu____2611 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2629 -> aux true t1'
                 | uu____2636 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2651 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2682 =
                   let uu____2683 = FStar_Syntax_Subst.compress t1'  in
                   uu____2683.FStar_Syntax_Syntax.n  in
                 match uu____2682 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2700 -> aux true t1'
                 | uu____2707 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2722 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2767 =
                   let uu____2768 = FStar_Syntax_Subst.compress t1'  in
                   uu____2768.FStar_Syntax_Syntax.n  in
                 match uu____2767 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2785 -> aux true t1'
                 | uu____2792 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2807 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2822 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2837 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2852 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2867 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2894 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2925 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2946 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2977 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3004 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3041 ->
              let uu____3048 =
                let uu____3049 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3050 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3049 uu____3050
                 in
              failwith uu____3048
          | FStar_Syntax_Syntax.Tm_ascribed uu____3065 ->
              let uu____3092 =
                let uu____3093 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3094 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3093 uu____3094
                 in
              failwith uu____3092
          | FStar_Syntax_Syntax.Tm_delayed uu____3109 ->
              let uu____3134 =
                let uu____3135 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3136 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3135 uu____3136
                 in
              failwith uu____3134
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3151 =
                let uu____3152 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3153 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3152 uu____3153
                 in
              failwith uu____3151
           in
        let uu____3168 = whnf env t1  in aux false uu____3168
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3199 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3199 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3230 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3230 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3266 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3266, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3277 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3277 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3302 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3302 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____3383  ->
    match uu____3383 with
    | (t_base,refopt) ->
        let uu____3410 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3410 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3448 =
      let uu____3451 =
        let uu____3454 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3477  ->
                  match uu____3477 with | (uu____3484,uu____3485,x) -> x))
           in
        FStar_List.append wl.attempting uu____3454  in
      FStar_List.map (wl_prob_to_string wl) uu____3451  in
    FStar_All.pipe_right uu____3448 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3504 =
          let uu____3517 =
            let uu____3518 = FStar_Syntax_Subst.compress k  in
            uu____3518.FStar_Syntax_Syntax.n  in
          match uu____3517 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3571 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3571)
              else
                (let uu____3585 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3585 with
                 | (ys',t1,uu____3608) ->
                     let uu____3613 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3613))
          | uu____3654 ->
              let uu____3655 =
                let uu____3666 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3666)  in
              ((ys, t), uu____3655)
           in
        match uu____3504 with
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
                 let uu____3715 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3715 c  in
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
             let uu____3754 = p_guard prob  in
             match uu____3754 with
             | (uu____3759,uv) ->
                 ((let uu____3762 =
                     let uu____3763 = FStar_Syntax_Subst.compress uv  in
                     uu____3763.FStar_Syntax_Syntax.n  in
                   match uu____3762 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                       let bs = p_scope prob  in
                       let phi1 = u_abs k bs phi  in
                       ((let uu____3795 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3795
                         then
                           let uu____3796 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____3797 =
                             FStar_Syntax_Print.term_to_string uv  in
                           let uu____3798 =
                             FStar_Syntax_Print.term_to_string phi1  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3796
                             uu____3797 uu____3798
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3801 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___153_3804 = wl  in
                   {
                     attempting = (uu___153_3804.attempting);
                     wl_deferred = (uu___153_3804.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___153_3804.defer_ok);
                     smt_ok = (uu___153_3804.smt_ok);
                     tcenv = (uu___153_3804.tcenv)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3825 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3825
         then
           let uu____3826 = FStar_Util.string_of_int pid  in
           let uu____3827 =
             let uu____3828 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3828 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3826 uu____3827
         else ());
        commit sol;
        (let uu___154_3835 = wl  in
         {
           attempting = (uu___154_3835.attempting);
           wl_deferred = (uu___154_3835.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___154_3835.defer_ok);
           smt_ok = (uu___154_3835.smt_ok);
           tcenv = (uu___154_3835.tcenv)
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
             | (uu____3887,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3899 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____3899
              in
           (let uu____3905 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3905
            then
              let uu____3906 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3907 =
                let uu____3908 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3908 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3906 uu____3907
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3947 =
          let uu____3954 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3954 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3947
          (FStar_Util.for_some
             (fun uu____3990  ->
                match uu____3990 with
                | (uv,uu____3996) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____4009 'Auu____4010 .
    'Auu____4009 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____4010)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.typ ->
            (Prims.bool,Prims.string FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun t  ->
          let occurs_ok =
            let uu____4046 = occurs wl uk t  in Prims.op_Negation uu____4046
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____4053 =
                 let uu____4054 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____4055 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4054 uu____4055
                  in
               FStar_Pervasives_Native.Some uu____4053)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____4072 'Auu____4073 .
    'Auu____4072 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____4073)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.bv FStar_Util.set ->
            FStar_Syntax_Syntax.term ->
              (Prims.bool,Prims.bool,(Prims.string
                                        FStar_Pervasives_Native.option,
                                       FStar_Syntax_Syntax.bv FStar_Util.set,
                                       FStar_Syntax_Syntax.bv FStar_Util.set)
                                       FStar_Pervasives_Native.tuple3)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun fvs  ->
          fun t  ->
            let fvs_t = FStar_Syntax_Free.names t  in
            let uu____4132 = occurs_check env wl uk t  in
            match uu____4132 with
            | (occurs_ok,msg) ->
                let uu____4163 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____4163, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____4190 'Auu____4191 .
    (FStar_Syntax_Syntax.bv,'Auu____4190) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4191) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____4191) FStar_Pervasives_Native.tuple2
          Prims.list
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
      let uu____4279 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4333  ->
                fun uu____4334  ->
                  match (uu____4333, uu____4334) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4415 =
                        let uu____4416 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4416  in
                      if uu____4415
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4441 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4441
                         then
                           let uu____4454 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____4454)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4279 with | (isect,uu____4495) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4524 'Auu____4525 .
    (FStar_Syntax_Syntax.bv,'Auu____4524) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4525) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4582  ->
              fun uu____4583  ->
                match (uu____4582, uu____4583) with
                | ((a,uu____4601),(b,uu____4603)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4622 'Auu____4623 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4622) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4623)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4623)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4677 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4691  ->
                      match uu____4691 with
                      | (b,uu____4697) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4677
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4713 -> FStar_Pervasives_Native.None
  
let rec (pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4792 = pat_var_opt env seen hd1  in
            (match uu____4792 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4806 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4806
                   then
                     let uu____4807 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4807
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4827 =
      let uu____4828 = FStar_Syntax_Subst.compress t  in
      uu____4828.FStar_Syntax_Syntax.n  in
    match uu____4827 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4831 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4848;
           FStar_Syntax_Syntax.pos = uu____4849;
           FStar_Syntax_Syntax.vars = uu____4850;_},uu____4851)
        -> true
    | uu____4888 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option
                                                             FStar_Unionfind.p_uvar,
                                                            FStar_Syntax_Syntax.version)
                                                            FStar_Pervasives_Native.tuple2,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                              FStar_Syntax_Syntax.syntax,
                                                             FStar_Syntax_Syntax.aqual)
                                                             FStar_Pervasives_Native.tuple2
                                                             Prims.list)
      FStar_Pervasives_Native.tuple4)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____5014;
           FStar_Syntax_Syntax.vars = uu____5015;_},args)
        -> (t, uv, k, args)
    | uu____5083 -> failwith "Not a flex-uvar"
  
let (destruct_flex_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                FStar_Syntax_Syntax.syntax
                                                                FStar_Pervasives_Native.option
                                                                FStar_Unionfind.p_uvar,
                                                               FStar_Syntax_Syntax.version)
                                                               FStar_Pervasives_Native.tuple2,
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax,
                                                                FStar_Syntax_Syntax.aqual)
                                                                FStar_Pervasives_Native.tuple2
                                                                Prims.list)
         FStar_Pervasives_Native.tuple4,FStar_Syntax_Syntax.binders
                                          FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t  ->
      let uu____5164 = destruct_flex_t t  in
      match uu____5164 with
      | (t1,uv,k,args) ->
          let uu____5279 = pat_vars env [] args  in
          (match uu____5279 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____5377 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5466 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____5504 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5517 -> false
  
let string_of_option :
  'Auu____5524 .
    ('Auu____5524 -> Prims.string) ->
      'Auu____5524 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___127_5539  ->
      match uu___127_5539 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5545 = f x  in Prims.strcat "Some " uu____5545
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___128_5550  ->
    match uu___128_5550 with
    | MisMatch (d1,d2) ->
        let uu____5561 =
          let uu____5562 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5563 =
            let uu____5564 =
              let uu____5565 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5565 ")"  in
            Prims.strcat ") (" uu____5564  in
          Prims.strcat uu____5562 uu____5563  in
        Prims.strcat "MisMatch (" uu____5561
    | HeadMatch u ->
        let uu____5567 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____5567
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___129_5572  ->
    match uu___129_5572 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____5587 -> HeadMatch false
  
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
          let uu____5601 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5601 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5612 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5635 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5644 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5672 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5672
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5673 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5674 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5675 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5692 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5705 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5729) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5735,uu____5736) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5778) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5799;
             FStar_Syntax_Syntax.index = uu____5800;
             FStar_Syntax_Syntax.sort = t2;_},uu____5802)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5809 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5810 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5811 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5824 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5831 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5849 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5849
  
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
            let uu____5876 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5876
            then FullMatch
            else
              (let uu____5878 =
                 let uu____5887 =
                   let uu____5890 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5890  in
                 let uu____5891 =
                   let uu____5894 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5894  in
                 (uu____5887, uu____5891)  in
               MisMatch uu____5878)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5900),FStar_Syntax_Syntax.Tm_uinst (g,uu____5902)) ->
            let uu____5911 = head_matches env f g  in
            FStar_All.pipe_right uu____5911 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5914 = FStar_Const.eq_const c d  in
            if uu____5914
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5921),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5923)) ->
            let uu____5972 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5972
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5979),FStar_Syntax_Syntax.Tm_refine (y,uu____5981)) ->
            let uu____5990 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5990 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5992),uu____5993) ->
            let uu____5998 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5998 head_match
        | (uu____5999,FStar_Syntax_Syntax.Tm_refine (x,uu____6001)) ->
            let uu____6006 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6006 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6007,FStar_Syntax_Syntax.Tm_type
           uu____6008) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6009,FStar_Syntax_Syntax.Tm_arrow uu____6010) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6036),FStar_Syntax_Syntax.Tm_app (head',uu____6038))
            ->
            let uu____6079 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6079 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6081),uu____6082) ->
            let uu____6103 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6103 head_match
        | (uu____6104,FStar_Syntax_Syntax.Tm_app (head1,uu____6106)) ->
            let uu____6127 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6127 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6128,FStar_Syntax_Syntax.Tm_let
           uu____6129) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6154,FStar_Syntax_Syntax.Tm_match uu____6155) ->
            HeadMatch true
        | uu____6200 ->
            let uu____6205 =
              let uu____6214 = delta_depth_of_term env t11  in
              let uu____6217 = delta_depth_of_term env t21  in
              (uu____6214, uu____6217)  in
            MisMatch uu____6205
  
let head_matches_delta :
  'Auu____6234 .
    FStar_TypeChecker_Env.env ->
      'Auu____6234 ->
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
            let uu____6273 = FStar_Syntax_Util.head_and_args t  in
            match uu____6273 with
            | (head1,uu____6291) ->
                let uu____6312 =
                  let uu____6313 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6313.FStar_Syntax_Syntax.n  in
                (match uu____6312 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6319 =
                       FStar_TypeChecker_Env.lookup_definition
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant;
                         FStar_TypeChecker_Env.Eager_unfolding_only] env
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (match uu____6319 with
                      | FStar_Pervasives_Native.None  ->
                          ((let uu____6333 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelDelta")
                               in
                            if uu____6333
                            then
                              let uu____6334 =
                                FStar_Syntax_Print.term_to_string head1  in
                              FStar_Util.print1
                                "No definition found for %s\n" uu____6334
                            else ());
                           FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some uu____6336 ->
                          let t' =
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF;
                              FStar_TypeChecker_Normalize.Beta;
                              FStar_TypeChecker_Normalize.Eager_unfolding]
                              env t
                             in
                          ((let uu____6347 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelDelta")
                               in
                            if uu____6347
                            then
                              let uu____6348 =
                                FStar_Syntax_Print.term_to_string t  in
                              let uu____6349 =
                                FStar_Syntax_Print.term_to_string t'  in
                              FStar_Util.print2 "Inlined %s to %s\n"
                                uu____6348 uu____6349
                            else ());
                           FStar_Pervasives_Native.Some t'))
                 | uu____6351 -> FStar_Pervasives_Native.None)
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
            (let uu____6489 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6489
             then
               let uu____6490 = FStar_Syntax_Print.term_to_string t11  in
               let uu____6491 = FStar_Syntax_Print.term_to_string t21  in
               let uu____6492 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6490
                 uu____6491 uu____6492
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____6516 =
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
               match uu____6516 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____6561 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____6561 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env wl t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env wl t21
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
                  uu____6593),uu____6594)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6612 =
                      let uu____6621 = maybe_inline t11  in
                      let uu____6624 = maybe_inline t21  in
                      (uu____6621, uu____6624)  in
                    match uu____6612 with
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
                 (uu____6661,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____6662))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6680 =
                      let uu____6689 = maybe_inline t11  in
                      let uu____6692 = maybe_inline t21  in
                      (uu____6689, uu____6692)  in
                    match uu____6680 with
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
             | MisMatch uu____6741 -> fail1 n_delta r t11 t21
             | uu____6750 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6763 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6763
           then
             let uu____6764 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6765 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6766 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6773 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6791 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6791
                    (fun uu____6825  ->
                       match uu____6825 with
                       | (t11,t21) ->
                           let uu____6832 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6833 =
                             let uu____6834 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6834  in
                           Prims.strcat uu____6832 uu____6833))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____6764 uu____6765 uu____6766 uu____6773
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp 
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6874 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6918 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let (tc_to_string : tc -> Prims.string) =
  fun uu___130_6932  ->
    match uu___130_6932 with
    | T (t,uu____6934) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6958 = FStar_Syntax_Util.type_u ()  in
      match uu____6958 with
      | (t,uu____6964) ->
          let uu____6965 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6965
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6980 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6980 FStar_Pervasives_Native.fst
  
let rec (decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____7054 = head_matches env t1 t'  in
        match uu____7054 with
        | MisMatch uu____7055 -> false
        | uu____7064 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____7164,imp),T (t2,uu____7167)) -> (t2, imp)
                     | uu____7190 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7257  ->
                    match uu____7257 with
                    | (t2,uu____7271) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7318 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7318 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7403))::tcs2) ->
                       aux
                         (((let uu___155_7442 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_7442.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_7442.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7460 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___131_7517 =
                 match uu___131_7517 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____7636 = decompose1 [] bs1  in
               (rebuild, matches, uu____7636))
      | uu____7687 ->
          let rebuild uu___132_7695 =
            match uu___132_7695 with
            | [] -> t1
            | uu____7698 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___133_7733  ->
    match uu___133_7733 with
    | T (t,uu____7735) -> t
    | uu____7748 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___134_7753  ->
    match uu___134_7753 with
    | T (t,uu____7755) -> FStar_Syntax_Syntax.as_arg t
    | uu____7768 -> failwith "Impossible"
  
let (imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3)
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig  in
            let rel = p_rel orig  in
            let sub_prob scope1 args q =
              match q with
              | (uu____7900,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7929 = new_uvar r scope1 k  in
                  (match uu____7929 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7947 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7964 =
                         let uu____7965 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_21  ->
                              FStar_TypeChecker_Common.TProb _0_21)
                           uu____7965
                          in
                       ((T (gi_xs, mk_kind)), uu____7964))
              | (uu____7980,uu____7981,C uu____7982) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____8135 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8152;
                         FStar_Syntax_Syntax.vars = uu____8153;_})
                        ->
                        let uu____8176 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8176 with
                         | (T (gi_xs,uu____8202),prob) ->
                             let uu____8216 =
                               let uu____8217 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_22  -> C _0_22)
                                 uu____8217
                                in
                             (uu____8216, [prob])
                         | uu____8220 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8235;
                         FStar_Syntax_Syntax.vars = uu____8236;_})
                        ->
                        let uu____8259 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8259 with
                         | (T (gi_xs,uu____8285),prob) ->
                             let uu____8299 =
                               let uu____8300 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_23  -> C _0_23)
                                 uu____8300
                                in
                             (uu____8299, [prob])
                         | uu____8303 -> failwith "impossible")
                    | (uu____8314,uu____8315,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8317;
                         FStar_Syntax_Syntax.vars = uu____8318;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind)))))
                           in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____8453 =
                          let uu____8462 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8462 FStar_List.unzip
                           in
                        (match uu____8453 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8516 =
                                 let uu____8517 =
                                   let uu____8520 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8520 un_T  in
                                 let uu____8521 =
                                   let uu____8530 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8530
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8517;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8521;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8516
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8539 ->
                        let uu____8552 = sub_prob scope1 args q  in
                        (match uu____8552 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____8135 with
                   | (tc,probs) ->
                       let uu____8583 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8646,uu____8647),T
                            (t,uu____8649)) ->
                             let b1 =
                               ((let uu___156_8690 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___156_8690.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___156_8690.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8691 =
                               let uu____8698 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8698 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8691)
                         | uu____8733 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8583 with
                        | (bopt,scope2,args1) ->
                            let uu____8817 = aux scope2 args1 qs2  in
                            (match uu____8817 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8855 =
                                           let uu____8858 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8858  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8855
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (1)" f1;
                                        f1)
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let f1 =
                                         let uu____8883 =
                                           let uu____8886 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8887 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8886 :: uu____8887  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8883
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (2)" f1;
                                        f1)
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
            aux scope ps qs
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
     FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.arg Prims.list,
    (tc Prims.list -> FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ ->
                                                Prims.bool,(FStar_Syntax_Syntax.binder
                                                              FStar_Pervasives_Native.option,
                                                             variance,
                                                             tc)
                                                             FStar_Pervasives_Native.tuple3
                                                             Prims.list)
      FStar_Pervasives_Native.tuple3)
    FStar_Pervasives_Native.tuple3
let (rigid_rigid : Prims.int) = (Prims.parse_int "0") 
let (flex_rigid_eq : Prims.int) = (Prims.parse_int "1") 
let (flex_refine_inner : Prims.int) = (Prims.parse_int "2") 
let (flex_refine : Prims.int) = (Prims.parse_int "3") 
let (flex_rigid : Prims.int) = (Prims.parse_int "4") 
let (rigid_flex : Prims.int) = (Prims.parse_int "5") 
let (refine_flex : Prims.int) = (Prims.parse_int "6") 
let (flex_flex : Prims.int) = (Prims.parse_int "7") 
let compress_tprob :
  'Auu____8961 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8961)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8961)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___157_8984 = p  in
      let uu____8989 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8990 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___157_8984.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8989;
        FStar_TypeChecker_Common.relation =
          (uu___157_8984.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8990;
        FStar_TypeChecker_Common.element =
          (uu___157_8984.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___157_8984.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___157_8984.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___157_8984.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___157_8984.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___157_8984.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9006 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____9006
            (fun _0_24  -> FStar_TypeChecker_Common.TProb _0_24)
      | FStar_TypeChecker_Common.CProb uu____9015 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____9039 = compress_prob wl pr  in
        FStar_All.pipe_right uu____9039 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9049 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9049 with
           | (lh,uu____9069) ->
               let uu____9090 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9090 with
                | (rh,uu____9110) ->
                    let uu____9131 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9148,FStar_Syntax_Syntax.Tm_uvar uu____9149)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9186,uu____9187)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9208,FStar_Syntax_Syntax.Tm_uvar uu____9209)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9230,uu____9231)
                          ->
                          let uu____9248 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9248 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9297 ->
                                    let rank =
                                      let uu____9305 = is_top_level_prob prob
                                         in
                                      if uu____9305
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9307 =
                                      let uu___158_9312 = tp  in
                                      let uu____9317 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___158_9312.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___158_9312.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___158_9312.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9317;
                                        FStar_TypeChecker_Common.element =
                                          (uu___158_9312.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___158_9312.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___158_9312.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___158_9312.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___158_9312.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___158_9312.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9307)))
                      | (uu____9328,FStar_Syntax_Syntax.Tm_uvar uu____9329)
                          ->
                          let uu____9346 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9346 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9395 ->
                                    let uu____9402 =
                                      let uu___159_9409 = tp  in
                                      let uu____9414 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___159_9409.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9414;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___159_9409.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___159_9409.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___159_9409.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___159_9409.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___159_9409.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___159_9409.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___159_9409.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___159_9409.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9402)))
                      | (uu____9431,uu____9432) -> (rigid_rigid, tp)  in
                    (match uu____9131 with
                     | (rank,tp1) ->
                         let uu____9451 =
                           FStar_All.pipe_right
                             (let uu___160_9457 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___160_9457.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___160_9457.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___160_9457.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___160_9457.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___160_9457.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___160_9457.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___160_9457.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___160_9457.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___160_9457.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_25  ->
                                FStar_TypeChecker_Common.TProb _0_25)
                            in
                         (rank, uu____9451))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9467 =
            FStar_All.pipe_right
              (let uu___161_9473 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___161_9473.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___161_9473.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___161_9473.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___161_9473.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___161_9473.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___161_9473.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___161_9473.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___161_9473.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___161_9473.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_26  -> FStar_TypeChecker_Common.CProb _0_26)
             in
          (rigid_rigid, uu____9467)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9534 probs =
      match uu____9534 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9587 = rank wl hd1  in
               (match uu____9587 with
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
  
let (is_flex_rigid : Prims.int -> Prims.bool) =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid) 
let (is_rigid_flex : Prims.int -> Prims.bool) =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9703 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9717 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9731 -> false
  
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
                        let uu____9783 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9783 with
                        | (k,uu____9789) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9799 -> false)))
            | uu____9800 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9852 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9858 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9858 = (Prims.parse_int "0")))
                           in
                        if uu____9852 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9874 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9880 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9880 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9874)
               in
            let uu____9881 = filter1 u12  in
            let uu____9884 = filter1 u22  in (uu____9881, uu____9884)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9913 = filter_out_common_univs us1 us2  in
                (match uu____9913 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9972 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9972 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9975 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9985 =
                          let uu____9986 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9987 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9986
                            uu____9987
                           in
                        UFailed uu____9985))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____10011 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____10011 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____10037 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____10037 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____10040 ->
                let uu____10045 =
                  let uu____10046 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____10047 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____10046
                    uu____10047 msg
                   in
                UFailed uu____10045
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10048,uu____10049) ->
              let uu____10050 =
                let uu____10051 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10052 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10051 uu____10052
                 in
              failwith uu____10050
          | (FStar_Syntax_Syntax.U_unknown ,uu____10053) ->
              let uu____10054 =
                let uu____10055 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10056 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10055 uu____10056
                 in
              failwith uu____10054
          | (uu____10057,FStar_Syntax_Syntax.U_bvar uu____10058) ->
              let uu____10059 =
                let uu____10060 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10061 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10060 uu____10061
                 in
              failwith uu____10059
          | (uu____10062,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10063 =
                let uu____10064 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10065 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10064 uu____10065
                 in
              failwith uu____10063
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10089 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10089
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10111 = occurs_univ v1 u3  in
              if uu____10111
              then
                let uu____10112 =
                  let uu____10113 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10114 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10113 uu____10114
                   in
                try_umax_components u11 u21 uu____10112
              else
                (let uu____10116 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10116)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10136 = occurs_univ v1 u3  in
              if uu____10136
              then
                let uu____10137 =
                  let uu____10138 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10139 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10138 uu____10139
                   in
                try_umax_components u11 u21 uu____10137
              else
                (let uu____10141 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10141)
          | (FStar_Syntax_Syntax.U_max uu____10150,uu____10151) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10157 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10157
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10159,FStar_Syntax_Syntax.U_max uu____10160) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10166 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10166
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10168,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10169,FStar_Syntax_Syntax.U_name uu____10170) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10171) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10172) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10173,FStar_Syntax_Syntax.U_succ uu____10174) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10175,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
  
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
      let uu____10275 = bc1  in
      match uu____10275 with
      | (bs1,mk_cod1) ->
          let uu____10319 = bc2  in
          (match uu____10319 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10430 = aux xs ys  in
                     (match uu____10430 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10513 =
                       let uu____10520 = mk_cod1 xs  in ([], uu____10520)  in
                     let uu____10523 =
                       let uu____10530 = mk_cod2 ys  in ([], uu____10530)  in
                     (uu____10513, uu____10523)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    tprob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun problem  ->
      fun t1  ->
        fun t2  ->
          let has_type_guard t11 t21 =
            match problem.FStar_TypeChecker_Common.element with
            | FStar_Pervasives_Native.Some t ->
                FStar_Syntax_Util.mk_has_type t11 t t21
            | FStar_Pervasives_Native.None  ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t11
                   in
                let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                let uu____10587 =
                  let uu____10588 = FStar_Syntax_Syntax.bv_to_name x  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10588 t21  in
                FStar_Syntax_Util.mk_forall u_x x uu____10587
             in
          match problem.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ  ->
              let uu____10591 =
                mk_eq2 (FStar_TypeChecker_Common.TProb problem) t1 t2  in
              FStar_All.pipe_left
                (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                uu____10591
          | FStar_TypeChecker_Common.SUB  ->
              let uu____10594 = has_type_guard t1 t2  in
              FStar_All.pipe_left
                (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                uu____10594
          | FStar_TypeChecker_Common.SUBINV  ->
              let uu____10605 = has_type_guard t2 t1  in
              FStar_All.pipe_left
                (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                uu____10605
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10786 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10786
       then
         let uu____10787 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10787
       else ());
      (let uu____10789 = next_prob probs  in
       match uu____10789 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___162_10810 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___162_10810.wl_deferred);
               ctr = (uu___162_10810.ctr);
               defer_ok = (uu___162_10810.defer_ok);
               smt_ok = (uu___162_10810.smt_ok);
               tcenv = (uu___162_10810.tcenv)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____10821 = solve_flex_rigid_join env tp probs1  in
                  (match uu____10821 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10826 = solve_rigid_flex_meet env tp probs1
                        in
                     match uu____10826 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10831,uu____10832) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10849 ->
                let uu____10858 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10917  ->
                          match uu____10917 with
                          | (c,uu____10925,uu____10926) -> c < probs.ctr))
                   in
                (match uu____10858 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10967 =
                            FStar_List.map
                              (fun uu____10982  ->
                                 match uu____10982 with
                                 | (uu____10993,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10967
                      | uu____10996 ->
                          let uu____11005 =
                            let uu___163_11006 = probs  in
                            let uu____11007 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11028  ->
                                      match uu____11028 with
                                      | (uu____11035,uu____11036,y) -> y))
                               in
                            {
                              attempting = uu____11007;
                              wl_deferred = rest;
                              ctr = (uu___163_11006.ctr);
                              defer_ok = (uu___163_11006.defer_ok);
                              smt_ok = (uu___163_11006.smt_ok);
                              tcenv = (uu___163_11006.tcenv)
                            }  in
                          solve env uu____11005))))

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
            let uu____11043 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11043 with
            | USolved wl1 ->
                let uu____11045 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11045
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
                  let uu____11097 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11097 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11100 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11112;
                  FStar_Syntax_Syntax.vars = uu____11113;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11116;
                  FStar_Syntax_Syntax.vars = uu____11117;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11129,uu____11130) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11137,FStar_Syntax_Syntax.Tm_uinst uu____11138) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11145 -> USolved wl

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
            ((let uu____11155 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11155
              then
                let uu____11156 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11156 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11165 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11165
         then
           let uu____11166 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____11166
         else ());
        (let uu____11168 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____11168 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____11234 = head_matches_delta env () t1 t2  in
               match uu____11234 with
               | (mr,ts) ->
                   (match mr with
                    | HeadMatch (true ) -> FStar_Pervasives_Native.None
                    | MisMatch uu____11281 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch (false ) ->
                        let uu____11330 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____11345 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____11346 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____11345, uu____11346)
                          | FStar_Pervasives_Native.None  ->
                              let uu____11351 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____11352 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____11351, uu____11352)
                           in
                        (match uu____11330 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11382 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_30  ->
                                    FStar_TypeChecker_Common.TProb _0_30)
                                 uu____11382
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11413 =
                                    let uu____11422 =
                                      let uu____11425 =
                                        let uu____11432 =
                                          let uu____11433 =
                                            let uu____11440 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____11440)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11433
                                           in
                                        FStar_Syntax_Syntax.mk uu____11432
                                         in
                                      uu____11425
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____11448 =
                                      let uu____11451 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____11451]  in
                                    (uu____11422, uu____11448)  in
                                  FStar_Pervasives_Native.Some uu____11413
                              | (uu____11464,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11466)) ->
                                  let uu____11471 =
                                    let uu____11478 =
                                      let uu____11481 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____11481]  in
                                    (t11, uu____11478)  in
                                  FStar_Pervasives_Native.Some uu____11471
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11491),uu____11492) ->
                                  let uu____11497 =
                                    let uu____11504 =
                                      let uu____11507 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____11507]  in
                                    (t21, uu____11504)  in
                                  FStar_Pervasives_Native.Some uu____11497
                              | uu____11516 ->
                                  let uu____11521 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____11521 with
                                   | (head1,uu____11545) ->
                                       let uu____11566 =
                                         let uu____11567 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____11567.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____11566 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11578;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11580;_}
                                            when i > (Prims.parse_int "0") ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0")
                                               in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11
                                               in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21
                                               in
                                            disjoin t12 t22
                                        | uu____11587 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11600) ->
                  let uu____11625 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___135_11651  ->
                            match uu___135_11651 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11658 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____11658 with
                                      | (u',uu____11674) ->
                                          let uu____11695 =
                                            let uu____11696 = whnf env u'  in
                                            uu____11696.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11695 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11700) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11725 -> false))
                                 | uu____11726 -> false)
                            | uu____11729 -> false))
                     in
                  (match uu____11625 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11767 tps =
                         match uu____11767 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11815 =
                                    let uu____11824 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____11824  in
                                  (match uu____11815 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11859 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11868 =
                         let uu____11877 =
                           let uu____11884 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11884, [])  in
                         make_lower_bound uu____11877 lower_bounds  in
                       (match uu____11868 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11896 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11896
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             FStar_Pervasives_Native.None)
                        | FStar_Pervasives_Native.Some (lhs_bound,sub_probs)
                            ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs
                                FStar_Pervasives_Native.None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____11916 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11916
                              then
                                let wl' =
                                  let uu___164_11918 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___164_11918.wl_deferred);
                                    ctr = (uu___164_11918.ctr);
                                    defer_ok = (uu___164_11918.defer_ok);
                                    smt_ok = (uu___164_11918.smt_ok);
                                    tcenv = (uu___164_11918.tcenv)
                                  }  in
                                let uu____11919 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11919
                              else ());
                             (let uu____11921 =
                                solve_t env eq_prob
                                  (let uu___165_11923 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___165_11923.wl_deferred);
                                     ctr = (uu___165_11923.ctr);
                                     defer_ok = (uu___165_11923.defer_ok);
                                     smt_ok = (uu___165_11923.smt_ok);
                                     tcenv = (uu___165_11923.tcenv)
                                   })
                                 in
                              match uu____11921 with
                              | Success uu____11926 ->
                                  let wl1 =
                                    let uu___166_11928 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___166_11928.wl_deferred);
                                      ctr = (uu___166_11928.ctr);
                                      defer_ok = (uu___166_11928.defer_ok);
                                      smt_ok = (uu___166_11928.smt_ok);
                                      tcenv = (uu___166_11928.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11930 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11935 -> FStar_Pervasives_Native.None))))
              | uu____11936 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11945 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11945
         then
           let uu____11946 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11946
         else ());
        (let uu____11948 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11948 with
         | (u,args) ->
             let uu____11987 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11987 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____12036 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____12036 with
                    | (h1,args1) ->
                        let uu____12077 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____12077 with
                         | (h2,uu____12097) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____12124 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____12124
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____12142 =
                                          let uu____12145 =
                                            let uu____12146 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_31  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_31) uu____12146
                                             in
                                          [uu____12145]  in
                                        FStar_Pervasives_Native.Some
                                          uu____12142))
                                  else FStar_Pervasives_Native.None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____12179 =
                                          let uu____12182 =
                                            let uu____12183 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_32  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_32) uu____12183
                                             in
                                          [uu____12182]  in
                                        FStar_Pervasives_Native.Some
                                          uu____12179))
                                  else FStar_Pervasives_Native.None
                              | uu____12197 -> FStar_Pervasives_Native.None))
                     in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort
                           in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____12291 =
                               let uu____12300 =
                                 let uu____12303 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____12303  in
                               (uu____12300, m1)  in
                             FStar_Pervasives_Native.Some uu____12291)
                    | (uu____12316,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12318)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12366),uu____12367) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12414 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12467) ->
                       let uu____12492 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___136_12518  ->
                                 match uu___136_12518 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12525 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____12525 with
                                           | (u',uu____12541) ->
                                               let uu____12562 =
                                                 let uu____12563 =
                                                   whnf env u'  in
                                                 uu____12563.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____12562 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12567) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12592 -> false))
                                      | uu____12593 -> false)
                                 | uu____12596 -> false))
                          in
                       (match uu____12492 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12638 tps =
                              match uu____12638 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12700 =
                                         let uu____12711 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____12711  in
                                       (match uu____12700 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12762 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____12773 =
                              let uu____12784 =
                                let uu____12793 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____12793, [])  in
                              make_upper_bound uu____12784 upper_bounds  in
                            (match uu____12773 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12807 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12807
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some
                                 (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     FStar_Pervasives_Native.None
                                     tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____12833 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12833
                                   then
                                     let wl' =
                                       let uu___167_12835 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___167_12835.wl_deferred);
                                         ctr = (uu___167_12835.ctr);
                                         defer_ok = (uu___167_12835.defer_ok);
                                         smt_ok = (uu___167_12835.smt_ok);
                                         tcenv = (uu___167_12835.tcenv)
                                       }  in
                                     let uu____12836 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12836
                                   else ());
                                  (let uu____12838 =
                                     solve_t env eq_prob
                                       (let uu___168_12840 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___168_12840.wl_deferred);
                                          ctr = (uu___168_12840.ctr);
                                          defer_ok =
                                            (uu___168_12840.defer_ok);
                                          smt_ok = (uu___168_12840.smt_ok);
                                          tcenv = (uu___168_12840.tcenv)
                                        })
                                      in
                                   match uu____12838 with
                                   | Success uu____12843 ->
                                       let wl1 =
                                         let uu___169_12845 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___169_12845.wl_deferred);
                                           ctr = (uu___169_12845.ctr);
                                           defer_ok =
                                             (uu___169_12845.defer_ok);
                                           smt_ok = (uu___169_12845.smt_ok);
                                           tcenv = (uu___169_12845.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____12847 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12852 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12853 -> failwith "Impossible: Not a flex-rigid")))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____12871 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12871
               then
                 let uu____12872 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12873 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12872 (rel_to_string (p_rel orig)) uu____12873
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____12943 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____12943
                       then
                         let uu____12944 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____12944
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___170_12998 = hd1  in
                       let uu____12999 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___170_12998.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___170_12998.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12999
                       }  in
                     let hd21 =
                       let uu___171_13003 = hd2  in
                       let uu____13004 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___171_13003.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___171_13003.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13004
                       }  in
                     let prob =
                       let uu____13008 =
                         let uu____13013 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____13013 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33)
                         uu____13008
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____13024 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____13024
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____13028 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____13028 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____13066 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____13071 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____13066 uu____13071
                             in
                          ((let uu____13081 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13081
                            then
                              let uu____13082 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____13083 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____13082 uu____13083
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____13106 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____13116 = aux scope env [] bs1 bs2  in
               match uu____13116 with
               | FStar_Util.Inr msg -> giveup env msg orig
               | FStar_Util.Inl (sub_probs,phi) ->
                   let wl1 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                      in
                   solve env (attempt sub_probs wl1))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13141 = compress_tprob wl problem  in
         solve_t' env uu____13141 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____13189 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____13189
            then
              let uu____13190 = FStar_Syntax_Print.term_to_string t1  in
              let uu____13191 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____13192 = FStar_Syntax_Print.term_to_string t2  in
              let uu____13193 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____13190 uu____13191 uu____13192 uu____13193
            else ());
           (let uu____13196 = FStar_Syntax_Util.head_and_args t1  in
            match uu____13196 with
            | (head1,args1) ->
                let uu____13233 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____13233 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____13287 =
                         let uu____13288 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13289 = args_to_string args1  in
                         let uu____13290 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____13291 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____13288 uu____13289 uu____13290 uu____13291
                          in
                       giveup env1 uu____13287 orig
                     else
                       (let uu____13293 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____13299 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____13299 = FStar_Syntax_Util.Equal)
                           in
                        if uu____13293
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___172_13301 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___172_13301.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___172_13301.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___172_13301.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___172_13301.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___172_13301.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___172_13301.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___172_13301.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___172_13301.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____13305 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____13305 with
                              | USolved wl2 ->
                                  let uu____13307 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____13307
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____13311 = base_and_refinement env1 t1  in
                           match uu____13311 with
                           | (base1,refinement1) ->
                               let uu____13336 = base_and_refinement env1 t2
                                  in
                               (match uu____13336 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         if need_unif
                                         then
                                           let subprobs =
                                             FStar_List.map2
                                               (fun uu____13415  ->
                                                  fun uu____13416  ->
                                                    match (uu____13415,
                                                            uu____13416)
                                                    with
                                                    | ((a,uu____13442),
                                                       (a',uu____13444)) ->
                                                        let uu____13465 =
                                                          let uu____13470 =
                                                            p_scope orig  in
                                                          mk_problem
                                                            uu____13470 orig
                                                            a
                                                            FStar_TypeChecker_Common.EQ
                                                            a'
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        FStar_All.pipe_left
                                                          (fun _0_34  ->
                                                             FStar_TypeChecker_Common.TProb
                                                               _0_34)
                                                          uu____13465)
                                               ((head1,
                                                  FStar_Pervasives_Native.None)
                                               :: args1)
                                               ((head2,
                                                  FStar_Pervasives_Native.None)
                                               :: args2)
                                              in
                                           ((let uu____13500 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel")
                                                in
                                             if uu____13500
                                             then
                                               let uu____13501 =
                                                 FStar_Syntax_Print.list_to_string
                                                   (prob_to_string env1)
                                                   subprobs
                                                  in
                                               FStar_Util.print1
                                                 "Adding subproblems for arguments: %s"
                                                 uu____13501
                                             else ());
                                            (let formula =
                                               let uu____13504 =
                                                 FStar_List.map
                                                   (fun p  ->
                                                      FStar_Pervasives_Native.fst
                                                        (p_guard p)) subprobs
                                                  in
                                               FStar_Syntax_Util.mk_conj_l
                                                 uu____13504
                                                in
                                             let wl2 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    formula) [] wl1
                                                in
                                             solve env1
                                               (attempt subprobs wl2)))
                                         else
                                           (let uu____13511 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____13511 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let subprobs =
                                                  FStar_List.map2
                                                    (fun uu____13533  ->
                                                       fun uu____13534  ->
                                                         match (uu____13533,
                                                                 uu____13534)
                                                         with
                                                         | ((a,uu____13552),
                                                            (a',uu____13554))
                                                             ->
                                                             let uu____13563
                                                               =
                                                               let uu____13568
                                                                 =
                                                                 p_scope orig
                                                                  in
                                                               mk_problem
                                                                 uu____13568
                                                                 orig a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             FStar_All.pipe_left
                                                               (fun _0_35  ->
                                                                  FStar_TypeChecker_Common.TProb
                                                                    _0_35)
                                                               uu____13563)
                                                    args1 args2
                                                   in
                                                ((let uu____13574 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____13574
                                                  then
                                                    let uu____13575 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____13575
                                                  else ());
                                                 (let formula =
                                                    let uu____13578 =
                                                      FStar_List.map
                                                        (fun p  ->
                                                           FStar_Pervasives_Native.fst
                                                             (p_guard p))
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____13578
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  solve env1
                                                    (attempt subprobs wl3))))
                                     | uu____13584 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___173_13620 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___173_13620.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___173_13620.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___173_13620.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___173_13620.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.scope
                                                =
                                                (uu___173_13620.FStar_TypeChecker_Common.scope);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___173_13620.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___173_13620.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___173_13620.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____13660 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____13660
            then
              let uu____13661 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____13662 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____13663 = FStar_Syntax_Print.term_to_string t1  in
              let uu____13664 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____13661 uu____13662 uu____13663 uu____13664
            else ());
           (let uu____13666 = head_matches_delta env1 wl1 t1 t2  in
            match uu____13666 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____13697,uu____13698) ->
                     let rec may_relate head3 =
                       let uu____13725 =
                         let uu____13726 = FStar_Syntax_Subst.compress head3
                            in
                         uu____13726.FStar_Syntax_Syntax.n  in
                       match uu____13725 with
                       | FStar_Syntax_Syntax.Tm_name uu____13729 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____13730 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____13753;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____13754;
                             FStar_Syntax_Syntax.fv_qual = uu____13755;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____13758;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____13759;
                             FStar_Syntax_Syntax.fv_qual = uu____13760;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____13764,uu____13765) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____13807) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____13813) ->
                           may_relate t
                       | uu____13818 -> false  in
                     let uu____13819 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____13819
                     then
                       let guard = guard_of_prob env1 problem t1 t2  in
                       let uu____13823 = solve_prob orig guard [] wl1  in
                       solve env1 uu____13823
                     else
                       (let uu____13825 =
                          let uu____13826 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____13827 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____13826 uu____13827
                           in
                        giveup env1 uu____13825 orig)
                 | (HeadMatch uu____13828,FStar_Pervasives_Native.Some
                    (t11,t21)) ->
                     solve_t env1
                       (let uu___174_13842 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___174_13842.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___174_13842.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___174_13842.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___174_13842.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___174_13842.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___174_13842.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___174_13842.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___174_13842.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___174_13856 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___174_13856.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___174_13856.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___174_13856.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___174_13856.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___174_13856.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___174_13856.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___174_13856.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___174_13856.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let force_quasi_pattern xs_opt uu____13912 =
           match uu____13912 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____13956 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____13956 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____14068  ->
                      let uu____14069 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____14069);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____14137  ->
                                match uu____14137 with
                                | (x,imp) ->
                                    let uu____14148 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____14148, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____14161 = FStar_Syntax_Util.type_u ()  in
                        match uu____14161 with
                        | (t1,uu____14167) ->
                            let uu____14168 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____14168
                         in
                      let uu____14173 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____14173 with
                       | (t',tm_u1) ->
                           let uu____14186 = destruct_flex_t t'  in
                           (match uu____14186 with
                            | (uu____14223,u1,k1,uu____14226) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____14285 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____14285
                                   in
                                let sol =
                                  let uu____14289 =
                                    let uu____14298 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____14298)  in
                                  TERM uu____14289  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____14433  ->
                            let uu____14434 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____14435 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____14434 uu____14435);
                       (let uu____14448 = pat_var_opt env pat_args hd1  in
                        match uu____14448 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____14468  ->
                                  FStar_Util.print_string
                                    "not a pattern var\n");
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1)
                        | FStar_Pervasives_Native.Some y ->
                            let maybe_pat =
                              match xs_opt with
                              | FStar_Pervasives_Native.None  -> true
                              | FStar_Pervasives_Native.Some xs ->
                                  FStar_All.pipe_right xs
                                    (FStar_Util.for_some
                                       (fun uu____14511  ->
                                          match uu____14511 with
                                          | (x,uu____14517) ->
                                              FStar_Syntax_Syntax.bv_eq x
                                                (FStar_Pervasives_Native.fst
                                                   y)))
                               in
                            if Prims.op_Negation maybe_pat
                            then
                              aux pat_args pat_args_set pattern_vars
                                pattern_var_set (formal :: seen_formals)
                                formals1 res_t tl1
                            else
                              (debug1
                                 (fun uu____14532  ->
                                    let uu____14533 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____14546 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____14533
                                      uu____14546);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____14550 =
                                  let uu____14551 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____14551  in
                                if uu____14550
                                then
                                  (debug1
                                     (fun uu____14563  ->
                                        let uu____14564 =
                                          let uu____14567 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____14580 =
                                            let uu____14583 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____14584 =
                                              let uu____14587 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____14588 =
                                                let uu____14591 =
                                                  names_to_string fvs  in
                                                let uu____14592 =
                                                  let uu____14595 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____14595]  in
                                                uu____14591 :: uu____14592
                                                 in
                                              uu____14587 :: uu____14588  in
                                            uu____14583 :: uu____14584  in
                                          uu____14567 :: uu____14580  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____14564);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____14597 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____14600 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____14597 (formal ::
                                     pattern_vars) uu____14600 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____14607::uu____14608) ->
                      let uu____14639 =
                        let uu____14652 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____14652  in
                      (match uu____14639 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____14691 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____14698::uu____14699,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____14722 =
                 let uu____14735 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____14735  in
               (match uu____14722 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____14771  ->
                          let uu____14772 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14773 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14774 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14775 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14772 uu____14773 uu____14774 uu____14775);
                     (let uu____14776 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____14779 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____14776 [] uu____14779 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____14825 = lhs  in
           match uu____14825 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____14835 ->
                     let uu____14836 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____14836 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____14867 = p  in
           match uu____14867 with
           | (((u,k),xs,c),ps,(h,uu____14878,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14966 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____14966 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____14989 = h gs_xs  in
                      let uu____14990 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                         in
                      FStar_Syntax_Util.abs xs1 uu____14989 uu____14990  in
                    ((let uu____14996 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14996
                      then
                        let uu____14997 =
                          let uu____15000 =
                            let uu____15001 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____15001
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____15006 =
                            let uu____15009 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____15010 =
                              let uu____15013 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____15014 =
                                let uu____15017 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____15018 =
                                  let uu____15021 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____15022 =
                                    let uu____15025 =
                                      let uu____15026 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____15026
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____15031 =
                                      let uu____15034 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____15034]  in
                                    uu____15025 :: uu____15031  in
                                  uu____15021 :: uu____15022  in
                                uu____15017 :: uu____15018  in
                              uu____15013 :: uu____15014  in
                            uu____15009 :: uu____15010  in
                          uu____15000 :: uu____15006  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____14997
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___137_15064 =
           match uu___137_15064 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____15106 = p  in
           match uu____15106 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____15203 = FStar_List.nth ps i  in
               (match uu____15203 with
                | (pi,uu____15207) ->
                    let uu____15212 = FStar_List.nth xs i  in
                    (match uu____15212 with
                     | (xi,uu____15224) ->
                         let rec gs k =
                           let uu____15239 =
                             let uu____15252 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____15252  in
                           match uu____15239 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____15331)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____15344 = new_uvar r xs k_a  in
                                     (match uu____15344 with
                                      | (gi_xs,gi) ->
                                          let gi_xs1 =
                                            FStar_TypeChecker_Normalize.eta_expand
                                              env1 gi_xs
                                             in
                                          let gi_ps =
                                            FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps FStar_Pervasives_Native.None
                                              r
                                             in
                                          let subst2 =
                                            (FStar_Syntax_Syntax.NT
                                               (a, gi_xs1))
                                            :: subst1  in
                                          let uu____15366 = aux subst2 tl1
                                             in
                                          (match uu____15366 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____15393 =
                                                 let uu____15396 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____15396 :: gi_xs'  in
                                               let uu____15397 =
                                                 let uu____15400 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____15400 :: gi_ps'  in
                                               (uu____15393, uu____15397)))
                                  in
                               aux [] bs
                            in
                         let uu____15405 =
                           let uu____15406 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____15406
                            in
                         if uu____15405
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____15410 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____15410 with
                            | (g_xs,uu____15422) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____15433 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____15434 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_37  ->
                                         FStar_Pervasives_Native.Some _0_37)
                                     in
                                  FStar_Syntax_Util.abs xs uu____15433
                                    uu____15434
                                   in
                                let sub1 =
                                  let uu____15440 =
                                    let uu____15445 = p_scope orig  in
                                    let uu____15446 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____15449 =
                                      let uu____15452 =
                                        FStar_List.map
                                          (fun uu____15467  ->
                                             match uu____15467 with
                                             | (uu____15476,uu____15477,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____15452  in
                                    mk_problem uu____15445 orig uu____15446
                                      (p_rel orig) uu____15449
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_38  ->
                                       FStar_TypeChecker_Common.TProb _0_38)
                                    uu____15440
                                   in
                                ((let uu____15492 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15492
                                  then
                                    let uu____15493 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____15494 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____15493 uu____15494
                                  else ());
                                 (let wl2 =
                                    let uu____15497 =
                                      let uu____15500 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____15500
                                       in
                                    solve_prob orig uu____15497
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____15509 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_39  ->
                                       FStar_Pervasives_Native.Some _0_39)
                                    uu____15509)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____15550 = lhs  in
           match uu____15550 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____15588 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____15588 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____15621 =
                         let uu____15670 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____15670)  in
                       FStar_Pervasives_Native.Some uu____15621
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____15824 =
                            let uu____15831 =
                              let uu____15832 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____15832.FStar_Syntax_Syntax.n  in
                            (uu____15831, args)  in
                          match uu____15824 with
                          | (uu____15843,[]) ->
                              let uu____15846 =
                                let uu____15857 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____15857)  in
                              FStar_Pervasives_Native.Some uu____15846
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____15878,uu____15879) ->
                              let uu____15900 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15900 with
                               | (uv1,uv_args) ->
                                   let uu____15943 =
                                     let uu____15944 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15944.FStar_Syntax_Syntax.n  in
                                   (match uu____15943 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15954) ->
                                        let uu____15979 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15979 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____16006  ->
                                                       let uu____16007 =
                                                         let uu____16008 =
                                                           let uu____16009 =
                                                             let uu____16014
                                                               =
                                                               let uu____16015
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____16015
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____16014
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____16009
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____16008
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____16007))
                                                in
                                             let c1 =
                                               let uu____16025 =
                                                 let uu____16026 =
                                                   let uu____16031 =
                                                     let uu____16032 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16032
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____16031
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____16026
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____16025
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____16045 =
                                                 let uu____16048 =
                                                   let uu____16049 =
                                                     let uu____16052 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16052
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____16049
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____16048
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____16045
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____16071 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____16076,uu____16077) ->
                              let uu____16096 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____16096 with
                               | (uv1,uv_args) ->
                                   let uu____16139 =
                                     let uu____16140 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____16140.FStar_Syntax_Syntax.n  in
                                   (match uu____16139 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____16150) ->
                                        let uu____16175 =
                                          pat_vars env [] uv_args  in
                                        (match uu____16175 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____16202  ->
                                                       let uu____16203 =
                                                         let uu____16204 =
                                                           let uu____16205 =
                                                             let uu____16210
                                                               =
                                                               let uu____16211
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____16211
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____16210
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____16205
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____16204
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____16203))
                                                in
                                             let c1 =
                                               let uu____16221 =
                                                 let uu____16222 =
                                                   let uu____16227 =
                                                     let uu____16228 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16228
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____16227
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____16222
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____16221
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____16241 =
                                                 let uu____16244 =
                                                   let uu____16245 =
                                                     let uu____16248 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16248
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____16245
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____16244
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____16241
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____16267 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____16274) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____16315 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____16315
                                  (fun _0_40  ->
                                     FStar_Pervasives_Native.Some _0_40)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____16351 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____16351 with
                                   | (args1,rest) ->
                                       let uu____16380 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____16380 with
                                        | (xs2,c2) ->
                                            let uu____16393 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____16393
                                              (fun uu____16417  ->
                                                 match uu____16417 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____16457 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____16457 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16525 =
                                         let uu____16530 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____16530
                                          in
                                       FStar_All.pipe_right uu____16525
                                         (fun _0_41  ->
                                            FStar_Pervasives_Native.Some
                                              _0_41))
                          | uu____16545 ->
                              let uu____16552 =
                                let uu____16557 =
                                  let uu____16558 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____16559 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____16560 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____16558 uu____16559 uu____16560
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____16557)
                                 in
                              FStar_Errors.raise_error uu____16552
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____16567 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____16567
                          (fun uu____16624  ->
                             match uu____16624 with
                             | (xs1,c1) ->
                                 let uu____16675 =
                                   let uu____16718 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____16718)
                                    in
                                 FStar_Pervasives_Native.Some uu____16675))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____16855 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____16875 = project orig env wl1 i st  in
                      match uu____16875 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____16889) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____16904 = imitate orig env wl1 st  in
                   match uu____16904 with
                   | Failed uu____16909 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____16948 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____16948 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____16971 = forced_lhs_pattern  in
                     (match uu____16971 with
                      | (lhs_t,uu____16973,uu____16974,uu____16975) ->
                          ((let uu____16977 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16977
                            then
                              let uu____16978 = lhs1  in
                              match uu____16978 with
                              | (t0,uu____16980,uu____16981,uu____16982) ->
                                  let uu____16983 = forced_lhs_pattern  in
                                  (match uu____16983 with
                                   | (t11,uu____16985,uu____16986,uu____16987)
                                       ->
                                       let uu____16988 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____16989 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____16988 uu____16989)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____16997 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____16997
                            then
                              ((let uu____16999 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16999
                                then
                                  let uu____17000 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____17001 = names_to_string rhs_vars
                                     in
                                  let uu____17002 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____17000 uu____17001 uu____17002
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____17006 =
                                  let uu____17007 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____17007 wl2  in
                                match uu____17006 with
                                | Failed uu____17008 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____17017 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____17017
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____17034 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____17034 with
                 | (hd1,uu____17050) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____17071 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____17084 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____17085 -> true
                      | uu____17102 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____17106 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____17106
                          then true
                          else
                            ((let uu____17109 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____17109
                              then
                                let uu____17110 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____17110
                              else ());
                             false))
                  in
               (match maybe_pat_vars with
                | FStar_Pervasives_Native.Some vars ->
                    let t11 = sn env t1  in
                    let t21 = sn env t2  in
                    let lhs1 = (t11, uv, k_uv, args_lhs)  in
                    let fvs1 = FStar_Syntax_Free.names t11  in
                    let fvs2 = FStar_Syntax_Free.names t21  in
                    let uu____17130 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____17130 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____17143 =
                             let uu____17144 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____17144
                              in
                           giveup_or_defer1 orig uu____17143
                         else
                           (let uu____17146 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____17146
                            then
                              let uu____17147 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____17147
                               then
                                 let uu____17148 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____17148
                               else
                                 ((let uu____17153 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____17153
                                   then
                                     let uu____17154 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____17155 = names_to_string fvs1
                                        in
                                     let uu____17156 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____17154 uu____17155 uu____17156
                                   else ());
                                  use_pattern_equality orig env wl1 lhs1 vars
                                    t21))
                            else
                              if
                                ((Prims.op_Negation patterns_only) &&
                                   wl1.defer_ok)
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                              then
                                solve env
                                  (defer
                                     "flex pattern/rigid: occurs or freevar check"
                                     orig wl1)
                              else
                                (let uu____17160 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____17160
                                 then
                                   ((let uu____17162 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____17162
                                     then
                                       let uu____17163 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____17164 = names_to_string fvs1
                                          in
                                       let uu____17165 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____17163 uu____17164 uu____17165
                                     else ());
                                    (let uu____17167 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____17167))
                                 else
                                   giveup env
                                     "free-variable check failed on a non-redex"
                                     orig)))
                | FStar_Pervasives_Native.None  when patterns_only ->
                    giveup env "not a pattern" orig
                | FStar_Pervasives_Native.None  ->
                    if wl1.defer_ok
                    then solve env (defer "not a pattern" orig wl1)
                    else
                      (let uu____17178 =
                         let uu____17179 = FStar_Syntax_Free.names t1  in
                         check_head uu____17179 t2  in
                       if uu____17178
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____17190 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17190
                           then
                             let uu____17191 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____17192 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____17191 uu____17192
                           else ());
                          (let uu____17200 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____17200))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____17291 uu____17292 r =
                match (uu____17291, uu____17292) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____17490 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____17490
                    then
                      let uu____17491 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____17491
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____17515 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____17515
                        then
                          let uu____17516 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____17517 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____17518 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____17519 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____17520 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____17516 uu____17517 uu____17518 uu____17519
                            uu____17520
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____17586 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____17586 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____17600 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____17600 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____17654 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____17654
                                      in
                                   let uu____17657 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____17657 k3)
                            else
                              (let uu____17661 =
                                 let uu____17662 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____17663 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____17664 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____17662 uu____17663 uu____17664
                                  in
                               failwith uu____17661)
                           in
                        let uu____17665 =
                          let uu____17672 =
                            let uu____17685 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____17685  in
                          match uu____17672 with
                          | (bs,k1') ->
                              let uu____17710 =
                                let uu____17723 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____17723
                                 in
                              (match uu____17710 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____17751 =
                                       let uu____17756 = p_scope orig  in
                                       mk_problem uu____17756 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_42  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_42) uu____17751
                                      in
                                   let uu____17761 =
                                     let uu____17766 =
                                       let uu____17767 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____17767.FStar_Syntax_Syntax.n  in
                                     let uu____17770 =
                                       let uu____17771 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____17771.FStar_Syntax_Syntax.n  in
                                     (uu____17766, uu____17770)  in
                                   (match uu____17761 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____17780,uu____17781) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____17784,FStar_Syntax_Syntax.Tm_type
                                       uu____17785) -> (k2'_ys, [sub_prob])
                                    | uu____17788 ->
                                        let uu____17793 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____17793 with
                                         | (t,uu____17805) ->
                                             let uu____17806 =
                                               new_uvar r zs t  in
                                             (match uu____17806 with
                                              | (k_zs,uu____17818) ->
                                                  let kprob =
                                                    let uu____17820 =
                                                      let uu____17825 =
                                                        p_scope orig  in
                                                      mk_problem uu____17825
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_43  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_43) uu____17820
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____17665 with
                        | (k_u',sub_probs) ->
                            let uu____17838 =
                              let uu____17849 =
                                let uu____17850 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____17850
                                 in
                              let uu____17859 =
                                let uu____17862 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____17862  in
                              let uu____17865 =
                                let uu____17868 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____17868  in
                              (uu____17849, uu____17859, uu____17865)  in
                            (match uu____17838 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____17887 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____17887 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____17906 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____17906
                                         then
                                           let wl2 =
                                             solve_prob orig
                                               FStar_Pervasives_Native.None
                                               [sol1] wl1
                                              in
                                           solve env wl2
                                         else
                                           (let sub2 = u_abs knew2 ys1 u_zs
                                               in
                                            let uu____17910 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____17910 with
                                            | (occurs_ok1,msg1) ->
                                                if
                                                  Prims.op_Negation
                                                    occurs_ok1
                                                then
                                                  giveup_or_defer1 orig
                                                    "flex-flex: failed occurs check"
                                                else
                                                  (let sol2 =
                                                     TERM ((u2, k2), sub2)
                                                      in
                                                   let wl2 =
                                                     solve_prob orig
                                                       FStar_Pervasives_Native.None
                                                       [sol1; sol2] wl1
                                                      in
                                                   solve env
                                                     (attempt sub_probs wl2))))))))
                 in
              let solve_one_pat uu____17967 uu____17968 =
                match (uu____17967, uu____17968) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____18086 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____18086
                      then
                        let uu____18087 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____18088 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____18087 uu____18088
                      else ());
                     (let uu____18090 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____18090
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____18109  ->
                               fun uu____18110  ->
                                 match (uu____18109, uu____18110) with
                                 | ((a,uu____18128),(t21,uu____18130)) ->
                                     let uu____18139 =
                                       let uu____18144 = p_scope orig  in
                                       let uu____18145 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____18144 orig
                                         uu____18145
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____18139
                                       (fun _0_44  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_44)) xs args2
                           in
                        let guard =
                          let uu____18151 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____18151  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____18166 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____18166 with
                         | (occurs_ok,uu____18174) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____18182 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____18182
                             then
                               let sol =
                                 let uu____18184 =
                                   let uu____18193 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____18193)  in
                                 TERM uu____18184  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____18200 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____18200
                                then
                                  let uu____18201 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____18201 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____18225,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____18251 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____18251
                                        then
                                          let uu____18252 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____18252
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____18259 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____18261 = lhs  in
              match uu____18261 with
              | (t1,u1,k1,args1) ->
                  let uu____18266 = rhs  in
                  (match uu____18266 with
                   | (t2,u2,k2,args2) ->
                       let maybe_pat_vars1 = pat_vars env [] args1  in
                       let maybe_pat_vars2 = pat_vars env [] args2  in
                       let r = t2.FStar_Syntax_Syntax.pos  in
                       (match (maybe_pat_vars1, maybe_pat_vars2) with
                        | (FStar_Pervasives_Native.Some
                           xs,FStar_Pervasives_Native.Some ys) ->
                            solve_both_pats wl (u1, k1, xs, args1)
                              (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                        | (FStar_Pervasives_Native.Some
                           xs,FStar_Pervasives_Native.None ) ->
                            solve_one_pat (t1, u1, k1, xs) rhs
                        | (FStar_Pervasives_Native.None
                           ,FStar_Pervasives_Native.Some ys) ->
                            solve_one_pat (t2, u2, k2, ys) lhs
                        | uu____18306 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____18316 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____18316 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____18334) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____18341 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____18341
                                     then
                                       let uu____18342 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____18342
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____18349 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18352 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18352
          then
            let uu____18353 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18353
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____18357 = FStar_Util.physical_equality t1 t2  in
             if uu____18357
             then
               let uu____18358 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____18358
             else
               ((let uu____18361 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____18361
                 then
                   let uu____18362 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____18363 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18364 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____18362
                     uu____18363 uu____18364
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____18367,uu____18368)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____18393,FStar_Syntax_Syntax.Tm_delayed uu____18394)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____18419,uu____18420)
                     ->
                     let uu____18447 =
                       let uu___175_18448 = problem  in
                       let uu____18449 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___175_18448.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18449;
                         FStar_TypeChecker_Common.relation =
                           (uu___175_18448.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___175_18448.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___175_18448.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___175_18448.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___175_18448.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___175_18448.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___175_18448.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___175_18448.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18447 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____18450,uu____18451) ->
                     let uu____18458 =
                       let uu___176_18459 = problem  in
                       let uu____18460 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_18459.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18460;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_18459.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_18459.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_18459.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_18459.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_18459.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_18459.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_18459.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_18459.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18458 wl
                 | (uu____18461,FStar_Syntax_Syntax.Tm_ascribed uu____18462)
                     ->
                     let uu____18489 =
                       let uu___177_18490 = problem  in
                       let uu____18491 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_18490.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_18490.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_18490.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18491;
                         FStar_TypeChecker_Common.element =
                           (uu___177_18490.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_18490.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_18490.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_18490.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_18490.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_18490.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18489 wl
                 | (uu____18492,FStar_Syntax_Syntax.Tm_meta uu____18493) ->
                     let uu____18500 =
                       let uu___178_18501 = problem  in
                       let uu____18502 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_18501.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_18501.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_18501.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18502;
                         FStar_TypeChecker_Common.element =
                           (uu___178_18501.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_18501.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_18501.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_18501.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_18501.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_18501.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18500 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____18504),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____18506)) ->
                     let uu____18515 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____18515
                 | (FStar_Syntax_Syntax.Tm_bvar uu____18516,uu____18517) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____18518,FStar_Syntax_Syntax.Tm_bvar uu____18519) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___138_18578 =
                       match uu___138_18578 with
                       | [] -> c
                       | bs ->
                           let uu____18600 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____18600
                        in
                     let uu____18609 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____18609 with
                      | ((bs11,c11),(bs21,c21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let c12 =
                                     FStar_Syntax_Subst.subst_comp subst1 c11
                                      in
                                   let c22 =
                                     FStar_Syntax_Subst.subst_comp subst1 c21
                                      in
                                   let rel =
                                     let uu____18753 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____18753
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____18755 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_45  ->
                                        FStar_TypeChecker_Common.CProb _0_45)
                                     uu____18755))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___139_18837 =
                       match uu___139_18837 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18871 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____18871 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____19009 =
                                     let uu____19014 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____19015 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____19014
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____19015
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_46  ->
                                        FStar_TypeChecker_Common.TProb _0_46)
                                     uu____19009))
                 | (FStar_Syntax_Syntax.Tm_abs uu____19020,uu____19021) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____19048 -> true
                       | uu____19065 -> false  in
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
                         (let uu____19116 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___179_19124 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___179_19124.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___179_19124.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___179_19124.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___179_19124.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___179_19124.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___179_19124.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___179_19124.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___179_19124.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___179_19124.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___179_19124.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___179_19124.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___179_19124.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___179_19124.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___179_19124.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___179_19124.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___179_19124.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___179_19124.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___179_19124.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___179_19124.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___179_19124.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___179_19124.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___179_19124.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___179_19124.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___179_19124.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___179_19124.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___179_19124.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___179_19124.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___179_19124.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___179_19124.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___179_19124.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___179_19124.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___179_19124.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___179_19124.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___179_19124.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____19116 with
                          | (uu____19127,ty,uu____19129) ->
                              let uu____19130 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19130)
                        in
                     let uu____19131 =
                       let uu____19148 = maybe_eta t1  in
                       let uu____19155 = maybe_eta t2  in
                       (uu____19148, uu____19155)  in
                     (match uu____19131 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___180_19197 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_19197.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___180_19197.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___180_19197.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_19197.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_19197.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_19197.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_19197.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_19197.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19220 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19220
                          then
                            let uu____19221 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19221 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19236 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19236.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19236.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19236.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19236.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19236.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19236.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19236.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19236.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19260 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19260
                          then
                            let uu____19261 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19261 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19276 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19276.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19276.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19276.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19276.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19276.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19276.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19276.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19276.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19280 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____19297,FStar_Syntax_Syntax.Tm_abs uu____19298) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____19325 -> true
                       | uu____19342 -> false  in
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
                         (let uu____19393 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___179_19401 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___179_19401.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___179_19401.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___179_19401.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___179_19401.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___179_19401.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___179_19401.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___179_19401.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___179_19401.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___179_19401.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___179_19401.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___179_19401.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___179_19401.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___179_19401.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___179_19401.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___179_19401.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___179_19401.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___179_19401.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___179_19401.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___179_19401.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___179_19401.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___179_19401.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___179_19401.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___179_19401.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___179_19401.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___179_19401.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___179_19401.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___179_19401.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___179_19401.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___179_19401.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___179_19401.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___179_19401.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___179_19401.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___179_19401.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___179_19401.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____19393 with
                          | (uu____19404,ty,uu____19406) ->
                              let uu____19407 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19407)
                        in
                     let uu____19408 =
                       let uu____19425 = maybe_eta t1  in
                       let uu____19432 = maybe_eta t2  in
                       (uu____19425, uu____19432)  in
                     (match uu____19408 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___180_19474 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_19474.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___180_19474.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___180_19474.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_19474.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_19474.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_19474.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_19474.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_19474.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19497 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19497
                          then
                            let uu____19498 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19498 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19513 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19513.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19513.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19513.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19513.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19513.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19513.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19513.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19513.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19537 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19537
                          then
                            let uu____19538 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19538 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19553 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19553.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19553.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19553.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19553.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19553.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19553.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19553.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19553.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19557 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____19589 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____19589) &&
                          (let uu____19601 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____19601))
                         &&
                         (let uu____19616 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____19616 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___140_19628 =
                                match uu___140_19628 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____19629 -> true
                                | uu____19630 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____19631 -> false)
                        in
                     let uu____19632 = as_refinement should_delta env wl t1
                        in
                     (match uu____19632 with
                      | (x11,phi1) ->
                          let uu____19639 =
                            as_refinement should_delta env wl t2  in
                          (match uu____19639 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____19647 =
                                   let uu____19652 = p_scope orig  in
                                   mk_problem uu____19652 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_47  ->
                                      FStar_TypeChecker_Common.TProb _0_47)
                                   uu____19647
                                  in
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
                                 let uu____19692 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____19692
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____19698 =
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
                                   let uu____19704 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19704 impl
                                    in
                                 let wl1 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl
                                    in
                                 solve env1 (attempt [base_prob] wl1)  in
                               if
                                 problem.FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ
                               then
                                 let ref_prob =
                                   let uu____19713 =
                                     let uu____19718 =
                                       let uu____19719 = p_scope orig  in
                                       let uu____19726 =
                                         let uu____19733 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____19733]  in
                                       FStar_List.append uu____19719
                                         uu____19726
                                        in
                                     mk_problem uu____19718 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_48  ->
                                        FStar_TypeChecker_Common.TProb _0_48)
                                     uu____19713
                                    in
                                 let uu____19742 =
                                   solve env1
                                     (let uu___182_19744 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___182_19744.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___182_19744.smt_ok);
                                        tcenv = (uu___182_19744.tcenv)
                                      })
                                    in
                                 (match uu____19742 with
                                  | Failed uu____19751 -> fallback ()
                                  | Success uu____19756 ->
                                      let guard =
                                        let uu____19760 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____19765 =
                                          let uu____19766 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____19766
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____19760
                                          uu____19765
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___183_19775 = wl1  in
                                        {
                                          attempting =
                                            (uu___183_19775.attempting);
                                          wl_deferred =
                                            (uu___183_19775.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___183_19775.defer_ok);
                                          smt_ok = (uu___183_19775.smt_ok);
                                          tcenv = (uu___183_19775.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19777,FStar_Syntax_Syntax.Tm_uvar uu____19778) ->
                     let uu____19811 = destruct_flex_t t1  in
                     let uu____19812 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19811 uu____19812
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19813;
                       FStar_Syntax_Syntax.pos = uu____19814;
                       FStar_Syntax_Syntax.vars = uu____19815;_},uu____19816),FStar_Syntax_Syntax.Tm_uvar
                    uu____19817) ->
                     let uu____19870 = destruct_flex_t t1  in
                     let uu____19871 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19870 uu____19871
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19872,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19873;
                       FStar_Syntax_Syntax.pos = uu____19874;
                       FStar_Syntax_Syntax.vars = uu____19875;_},uu____19876))
                     ->
                     let uu____19929 = destruct_flex_t t1  in
                     let uu____19930 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19929 uu____19930
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19931;
                       FStar_Syntax_Syntax.pos = uu____19932;
                       FStar_Syntax_Syntax.vars = uu____19933;_},uu____19934),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19935;
                       FStar_Syntax_Syntax.pos = uu____19936;
                       FStar_Syntax_Syntax.vars = uu____19937;_},uu____19938))
                     ->
                     let uu____20011 = destruct_flex_t t1  in
                     let uu____20012 = destruct_flex_t t2  in
                     flex_flex1 orig uu____20011 uu____20012
                 | (FStar_Syntax_Syntax.Tm_uvar uu____20013,uu____20014) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____20031 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____20031 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20038;
                       FStar_Syntax_Syntax.pos = uu____20039;
                       FStar_Syntax_Syntax.vars = uu____20040;_},uu____20041),uu____20042)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____20079 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____20079 t2 wl
                 | (uu____20086,FStar_Syntax_Syntax.Tm_uvar uu____20087) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____20104,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20105;
                       FStar_Syntax_Syntax.pos = uu____20106;
                       FStar_Syntax_Syntax.vars = uu____20107;_},uu____20108))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____20145,FStar_Syntax_Syntax.Tm_type uu____20146) ->
                     solve_t' env
                       (let uu___184_20164 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20164.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20164.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20164.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20164.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20164.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20164.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20164.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20164.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20164.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20165;
                       FStar_Syntax_Syntax.pos = uu____20166;
                       FStar_Syntax_Syntax.vars = uu____20167;_},uu____20168),FStar_Syntax_Syntax.Tm_type
                    uu____20169) ->
                     solve_t' env
                       (let uu___184_20207 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20207.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20207.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20207.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20207.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20207.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20207.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20207.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20207.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20207.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____20208,FStar_Syntax_Syntax.Tm_arrow uu____20209) ->
                     solve_t' env
                       (let uu___184_20239 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20239.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20239.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20239.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20239.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20239.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20239.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20239.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20239.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20239.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20240;
                       FStar_Syntax_Syntax.pos = uu____20241;
                       FStar_Syntax_Syntax.vars = uu____20242;_},uu____20243),FStar_Syntax_Syntax.Tm_arrow
                    uu____20244) ->
                     solve_t' env
                       (let uu___184_20294 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20294.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20294.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20294.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20294.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20294.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20294.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20294.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20294.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20294.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____20295,uu____20296) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20315 =
                          let uu____20316 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20316
                           in
                        if uu____20315
                        then
                          let uu____20317 =
                            FStar_All.pipe_left
                              (fun _0_49  ->
                                 FStar_TypeChecker_Common.TProb _0_49)
                              (let uu___185_20323 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___185_20323.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___185_20323.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___185_20323.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___185_20323.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___185_20323.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___185_20323.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___185_20323.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___185_20323.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___185_20323.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20324 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20317 uu____20324 t2
                            wl
                        else
                          (let uu____20332 = base_and_refinement env t2  in
                           match uu____20332 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20361 =
                                      FStar_All.pipe_left
                                        (fun _0_50  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_50)
                                        (let uu___186_20367 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___186_20367.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___186_20367.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___186_20367.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___186_20367.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___186_20367.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___186_20367.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___186_20367.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___186_20367.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___186_20367.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20368 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20361
                                      uu____20368 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___187_20382 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___187_20382.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___187_20382.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20385 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_51  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_51) uu____20385
                                       in
                                    let guard =
                                      let uu____20397 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20397
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20405;
                       FStar_Syntax_Syntax.pos = uu____20406;
                       FStar_Syntax_Syntax.vars = uu____20407;_},uu____20408),uu____20409)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20448 =
                          let uu____20449 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20449
                           in
                        if uu____20448
                        then
                          let uu____20450 =
                            FStar_All.pipe_left
                              (fun _0_52  ->
                                 FStar_TypeChecker_Common.TProb _0_52)
                              (let uu___185_20456 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___185_20456.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___185_20456.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___185_20456.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___185_20456.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___185_20456.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___185_20456.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___185_20456.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___185_20456.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___185_20456.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20457 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20450 uu____20457 t2
                            wl
                        else
                          (let uu____20465 = base_and_refinement env t2  in
                           match uu____20465 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20494 =
                                      FStar_All.pipe_left
                                        (fun _0_53  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_53)
                                        (let uu___186_20500 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___186_20500.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___186_20500.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___186_20500.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___186_20500.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___186_20500.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___186_20500.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___186_20500.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___186_20500.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___186_20500.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20501 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20494
                                      uu____20501 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___187_20515 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___187_20515.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___187_20515.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20518 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_54  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_54) uu____20518
                                       in
                                    let guard =
                                      let uu____20530 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20530
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____20538,FStar_Syntax_Syntax.Tm_uvar uu____20539) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20557 = base_and_refinement env t1  in
                        match uu____20557 with
                        | (t_base,uu____20569) ->
                            solve_t env
                              (let uu___188_20583 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_20583.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___188_20583.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_20583.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_20583.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___188_20583.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_20583.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_20583.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_20583.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____20584,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20585;
                       FStar_Syntax_Syntax.pos = uu____20586;
                       FStar_Syntax_Syntax.vars = uu____20587;_},uu____20588))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20626 = base_and_refinement env t1  in
                        match uu____20626 with
                        | (t_base,uu____20638) ->
                            solve_t env
                              (let uu___188_20652 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_20652.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___188_20652.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_20652.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_20652.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___188_20652.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_20652.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_20652.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_20652.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____20653,uu____20654) ->
                     let t21 =
                       let uu____20664 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____20664  in
                     solve_t env
                       (let uu___189_20688 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___189_20688.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___189_20688.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___189_20688.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___189_20688.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___189_20688.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___189_20688.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___189_20688.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___189_20688.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___189_20688.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____20689,FStar_Syntax_Syntax.Tm_refine uu____20690) ->
                     let t11 =
                       let uu____20700 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____20700  in
                     solve_t env
                       (let uu___190_20724 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___190_20724.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___190_20724.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___190_20724.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___190_20724.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___190_20724.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___190_20724.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___190_20724.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___190_20724.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___190_20724.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                     let sc_prob =
                       let uu____20804 =
                         let uu____20809 = p_scope orig  in
                         mk_problem uu____20809 orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                         uu____20804
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____20999 = br1  in
                           (match uu____20999 with
                            | (p1,w1,uu____21018) ->
                                let uu____21031 = br2  in
                                (match uu____21031 with
                                 | (p2,w2,uu____21046) ->
                                     let uu____21051 =
                                       let uu____21052 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____21052  in
                                     if uu____21051
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____21060 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____21060 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____21103 = br2  in
                                            (match uu____21103 with
                                             | (p21,w21,e2) ->
                                                 let w22 =
                                                   FStar_Util.map_opt w21
                                                     (FStar_Syntax_Subst.subst
                                                        s)
                                                    in
                                                 let e21 =
                                                   FStar_Syntax_Subst.subst s
                                                     e2
                                                    in
                                                 let scope =
                                                   let uu____21134 =
                                                     p_scope orig  in
                                                   let uu____21141 =
                                                     let uu____21148 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____21148
                                                      in
                                                   FStar_List.append
                                                     uu____21134 uu____21141
                                                    in
                                                 let uu____21159 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____21174,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____21187) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____21220 =
                                                         let uu____21223 =
                                                           let uu____21224 =
                                                             mk_problem scope
                                                               orig w12
                                                               FStar_TypeChecker_Common.EQ
                                                               w23
                                                               FStar_Pervasives_Native.None
                                                               "when clause"
                                                              in
                                                           FStar_All.pipe_left
                                                             (fun _0_56  ->
                                                                FStar_TypeChecker_Common.TProb
                                                                  _0_56)
                                                             uu____21224
                                                            in
                                                         [uu____21223]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21220
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____21159
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____21248 =
                                                          mk_problem scope
                                                            orig e1
                                                            FStar_TypeChecker_Common.EQ
                                                            e21
                                                            FStar_Pervasives_Native.None
                                                            "branch body"
                                                           in
                                                        FStar_All.pipe_left
                                                          (fun _0_57  ->
                                                             FStar_TypeChecker_Common.TProb
                                                               _0_57)
                                                          uu____21248
                                                         in
                                                      let uu____21259 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____21259
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____21320 -> FStar_Pervasives_Native.None  in
                     let by_smt uu____21356 =
                       let guard = guard_of_prob env problem t1 t2  in
                       let uu____21360 = solve_prob orig guard [] wl  in
                       solve env uu____21360  in
                     let uu____21361 = solve_branches brs1 brs2  in
                     (match uu____21361 with
                      | FStar_Pervasives_Native.None  ->
                          if wl.smt_ok
                          then by_smt ()
                          else
                            giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let formula =
                            let uu____21378 =
                              FStar_List.map
                                (fun p  ->
                                   FStar_Pervasives_Native.fst (p_guard p))
                                sub_probs1
                               in
                            FStar_Syntax_Util.mk_conj_l uu____21378  in
                          let tx = FStar_Syntax_Unionfind.new_transaction ()
                             in
                          let wl1 =
                            solve_prob orig
                              (FStar_Pervasives_Native.Some formula) [] wl
                             in
                          let uu____21385 =
                            solve env
                              (attempt sub_probs1
                                 (let uu___191_21387 = wl1  in
                                  {
                                    attempting = (uu___191_21387.attempting);
                                    wl_deferred =
                                      (uu___191_21387.wl_deferred);
                                    ctr = (uu___191_21387.ctr);
                                    defer_ok = (uu___191_21387.defer_ok);
                                    smt_ok = false;
                                    tcenv = (uu___191_21387.tcenv)
                                  }))
                             in
                          (match uu____21385 with
                           | Success ds ->
                               (FStar_Syntax_Unionfind.commit tx; Success ds)
                           | Failed uu____21390 ->
                               (FStar_Syntax_Unionfind.rollback tx; by_smt ())))
                 | (FStar_Syntax_Syntax.Tm_match uu____21396,uu____21397) ->
                     let head1 =
                       let uu____21423 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21423
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21467 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21467
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21509 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21509
                       then
                         let uu____21510 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21511 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21512 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21510 uu____21511 uu____21512
                       else ());
                      (let uu____21514 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21514
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21529 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21529
                          then
                            let guard =
                              let uu____21541 =
                                let uu____21542 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21542 = FStar_Syntax_Util.Equal  in
                              if uu____21541
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21546 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_Pervasives_Native.Some _0_58)
                                   uu____21546)
                               in
                            let uu____21549 = solve_prob orig guard [] wl  in
                            solve env uu____21549
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____21552,uu____21553) ->
                     let head1 =
                       let uu____21563 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21563
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21607 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21607
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21649 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21649
                       then
                         let uu____21650 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21651 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21652 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21650 uu____21651 uu____21652
                       else ());
                      (let uu____21654 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21654
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21669 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21669
                          then
                            let guard =
                              let uu____21681 =
                                let uu____21682 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21682 = FStar_Syntax_Util.Equal  in
                              if uu____21681
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21686 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_Pervasives_Native.Some _0_59)
                                   uu____21686)
                               in
                            let uu____21689 = solve_prob orig guard [] wl  in
                            solve env uu____21689
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____21692,uu____21693) ->
                     let head1 =
                       let uu____21697 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21697
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21741 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21741
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21783 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21783
                       then
                         let uu____21784 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21785 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21786 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21784 uu____21785 uu____21786
                       else ());
                      (let uu____21788 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21788
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21803 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21803
                          then
                            let guard =
                              let uu____21815 =
                                let uu____21816 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21816 = FStar_Syntax_Util.Equal  in
                              if uu____21815
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21820 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____21820)
                               in
                            let uu____21823 = solve_prob orig guard [] wl  in
                            solve env uu____21823
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____21826,uu____21827)
                     ->
                     let head1 =
                       let uu____21831 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21831
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21875 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21875
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21917 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21917
                       then
                         let uu____21918 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21919 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21920 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21918 uu____21919 uu____21920
                       else ());
                      (let uu____21922 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21922
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21937 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21937
                          then
                            let guard =
                              let uu____21949 =
                                let uu____21950 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21950 = FStar_Syntax_Util.Equal  in
                              if uu____21949
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21954 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____21954)
                               in
                            let uu____21957 = solve_prob orig guard [] wl  in
                            solve env uu____21957
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____21960,uu____21961) ->
                     let head1 =
                       let uu____21965 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21965
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22009 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22009
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22051 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22051
                       then
                         let uu____22052 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22053 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22054 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22052 uu____22053 uu____22054
                       else ());
                      (let uu____22056 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22056
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22071 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22071
                          then
                            let guard =
                              let uu____22083 =
                                let uu____22084 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22084 = FStar_Syntax_Util.Equal  in
                              if uu____22083
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22088 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____22088)
                               in
                            let uu____22091 = solve_prob orig guard [] wl  in
                            solve env uu____22091
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____22094,uu____22095) ->
                     let head1 =
                       let uu____22113 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22113
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22157 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22157
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22199 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22199
                       then
                         let uu____22200 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22201 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22202 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22200 uu____22201 uu____22202
                       else ());
                      (let uu____22204 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22204
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22219 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22219
                          then
                            let guard =
                              let uu____22231 =
                                let uu____22232 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22232 = FStar_Syntax_Util.Equal  in
                              if uu____22231
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22236 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   uu____22236)
                               in
                            let uu____22239 = solve_prob orig guard [] wl  in
                            solve env uu____22239
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22242,FStar_Syntax_Syntax.Tm_match uu____22243) ->
                     let head1 =
                       let uu____22269 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22269
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22313 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22313
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22355 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22355
                       then
                         let uu____22356 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22357 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22358 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22356 uu____22357 uu____22358
                       else ());
                      (let uu____22360 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22360
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22375 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22375
                          then
                            let guard =
                              let uu____22387 =
                                let uu____22388 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22388 = FStar_Syntax_Util.Equal  in
                              if uu____22387
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22392 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   uu____22392)
                               in
                            let uu____22395 = solve_prob orig guard [] wl  in
                            solve env uu____22395
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22398,FStar_Syntax_Syntax.Tm_uinst uu____22399) ->
                     let head1 =
                       let uu____22409 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22409
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22453 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22453
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22495 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22495
                       then
                         let uu____22496 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22497 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22498 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22496 uu____22497 uu____22498
                       else ());
                      (let uu____22500 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22500
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22515 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22515
                          then
                            let guard =
                              let uu____22527 =
                                let uu____22528 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22528 = FStar_Syntax_Util.Equal  in
                              if uu____22527
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22532 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   uu____22532)
                               in
                            let uu____22535 = solve_prob orig guard [] wl  in
                            solve env uu____22535
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22538,FStar_Syntax_Syntax.Tm_name uu____22539) ->
                     let head1 =
                       let uu____22543 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22543
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22587 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22587
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22629 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22629
                       then
                         let uu____22630 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22631 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22632 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22630 uu____22631 uu____22632
                       else ());
                      (let uu____22634 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22634
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22649 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22649
                          then
                            let guard =
                              let uu____22661 =
                                let uu____22662 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22662 = FStar_Syntax_Util.Equal  in
                              if uu____22661
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22666 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   uu____22666)
                               in
                            let uu____22669 = solve_prob orig guard [] wl  in
                            solve env uu____22669
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22672,FStar_Syntax_Syntax.Tm_constant uu____22673)
                     ->
                     let head1 =
                       let uu____22677 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22677
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22721 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22721
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22763 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22763
                       then
                         let uu____22764 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22765 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22766 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22764 uu____22765 uu____22766
                       else ());
                      (let uu____22768 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22768
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22783 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22783
                          then
                            let guard =
                              let uu____22795 =
                                let uu____22796 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22796 = FStar_Syntax_Util.Equal  in
                              if uu____22795
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22800 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   uu____22800)
                               in
                            let uu____22803 = solve_prob orig guard [] wl  in
                            solve env uu____22803
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22806,FStar_Syntax_Syntax.Tm_fvar uu____22807) ->
                     let head1 =
                       let uu____22811 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22811
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22855 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22855
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22897 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22897
                       then
                         let uu____22898 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22899 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22900 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22898 uu____22899 uu____22900
                       else ());
                      (let uu____22902 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22902
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22917 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22917
                          then
                            let guard =
                              let uu____22929 =
                                let uu____22930 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22930 = FStar_Syntax_Util.Equal  in
                              if uu____22929
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22934 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_Pervasives_Native.Some _0_68)
                                   uu____22934)
                               in
                            let uu____22937 = solve_prob orig guard [] wl  in
                            solve env uu____22937
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22940,FStar_Syntax_Syntax.Tm_app uu____22941) ->
                     let head1 =
                       let uu____22959 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22959
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____23003 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____23003
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____23045 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____23045
                       then
                         let uu____23046 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____23047 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____23048 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____23046 uu____23047 uu____23048
                       else ());
                      (let uu____23050 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____23050
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____23065 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____23065
                          then
                            let guard =
                              let uu____23077 =
                                let uu____23078 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____23078 = FStar_Syntax_Util.Equal  in
                              if uu____23077
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____23082 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_Pervasives_Native.Some _0_69)
                                   uu____23082)
                               in
                            let uu____23085 = solve_prob orig guard [] wl  in
                            solve env uu____23085
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____23088,FStar_Syntax_Syntax.Tm_let uu____23089) ->
                     let uu____23114 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____23114
                     then
                       let uu____23115 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____23115
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____23117,uu____23118) ->
                     let uu____23131 =
                       let uu____23136 =
                         let uu____23137 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____23138 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____23139 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____23140 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____23137 uu____23138 uu____23139 uu____23140
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____23136)
                        in
                     FStar_Errors.raise_error uu____23131
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____23141,FStar_Syntax_Syntax.Tm_let uu____23142) ->
                     let uu____23155 =
                       let uu____23160 =
                         let uu____23161 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____23162 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____23163 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____23164 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____23161 uu____23162 uu____23163 uu____23164
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____23160)
                        in
                     FStar_Errors.raise_error uu____23155
                       t1.FStar_Syntax_Syntax.pos
                 | uu____23165 -> giveup env "head tag mismatch" orig)))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          let uu____23201 = p_scope orig  in
          mk_problem uu____23201 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____23214 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23214
           then
             let uu____23215 =
               let uu____23216 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23216  in
             let uu____23217 =
               let uu____23218 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23218  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23215 uu____23217
           else ());
          (let uu____23220 =
             let uu____23221 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23221  in
           if uu____23220
           then
             let uu____23222 =
               let uu____23223 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23224 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23223 uu____23224
                in
             giveup env uu____23222 orig
           else
             (let ret_sub_prob =
                let uu____23227 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_70  -> FStar_TypeChecker_Common.TProb _0_70)
                  uu____23227
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____23254  ->
                     fun uu____23255  ->
                       match (uu____23254, uu____23255) with
                       | ((a1,uu____23273),(a2,uu____23275)) ->
                           let uu____23284 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_71  ->
                                FStar_TypeChecker_Common.TProb _0_71)
                             uu____23284)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____23297 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____23297  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23329 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23336)::[] -> wp1
              | uu____23353 ->
                  let uu____23362 =
                    let uu____23363 =
                      let uu____23364 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23364  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23363
                     in
                  failwith uu____23362
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23372 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23372]
              | x -> x  in
            let uu____23374 =
              let uu____23383 =
                let uu____23384 =
                  let uu____23385 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23385 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23384  in
              [uu____23383]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23374;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23386 = lift_c1 ()  in solve_eq uu____23386 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___141_23392  ->
                       match uu___141_23392 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23393 -> false))
                in
             let uu____23394 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23428)::uu____23429,(wp2,uu____23431)::uu____23432)
                   -> (wp1, wp2)
               | uu____23489 ->
                   let uu____23510 =
                     let uu____23515 =
                       let uu____23516 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23517 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23516 uu____23517
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23515)
                      in
                   FStar_Errors.raise_error uu____23510
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23394 with
             | (wpc1,wpc2) ->
                 let uu____23536 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23536
                 then
                   let uu____23539 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23539 wl
                 else
                   (let uu____23543 =
                      let uu____23550 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23550  in
                    match uu____23543 with
                    | (c2_decl,qualifiers) ->
                        let uu____23571 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23571
                        then
                          let c1_repr =
                            let uu____23575 =
                              let uu____23576 =
                                let uu____23577 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23577  in
                              let uu____23578 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23576 uu____23578
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23575
                             in
                          let c2_repr =
                            let uu____23580 =
                              let uu____23581 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23582 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23581 uu____23582
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23580
                             in
                          let prob =
                            let uu____23584 =
                              let uu____23589 =
                                let uu____23590 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____23591 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23590
                                  uu____23591
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23589
                               in
                            FStar_TypeChecker_Common.TProb uu____23584  in
                          let wl1 =
                            let uu____23593 =
                              let uu____23596 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____23596  in
                            solve_prob orig uu____23593 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23605 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23605
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23608 =
                                     let uu____23615 =
                                       let uu____23616 =
                                         let uu____23631 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23632 =
                                           let uu____23635 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23636 =
                                             let uu____23639 =
                                               let uu____23640 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23640
                                                in
                                             [uu____23639]  in
                                           uu____23635 :: uu____23636  in
                                         (uu____23631, uu____23632)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23616
                                        in
                                     FStar_Syntax_Syntax.mk uu____23615  in
                                   uu____23608 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23649 =
                                    let uu____23656 =
                                      let uu____23657 =
                                        let uu____23672 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23673 =
                                          let uu____23676 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____23677 =
                                            let uu____23680 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____23681 =
                                              let uu____23684 =
                                                let uu____23685 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23685
                                                 in
                                              [uu____23684]  in
                                            uu____23680 :: uu____23681  in
                                          uu____23676 :: uu____23677  in
                                        (uu____23672, uu____23673)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23657
                                       in
                                    FStar_Syntax_Syntax.mk uu____23656  in
                                  uu____23649 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23692 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_TypeChecker_Common.TProb _0_72)
                               uu____23692
                              in
                           let wl1 =
                             let uu____23702 =
                               let uu____23705 =
                                 let uu____23708 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23708 g  in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_Pervasives_Native.Some _0_73)
                                 uu____23705
                                in
                             solve_prob orig uu____23702 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23721 = FStar_Util.physical_equality c1 c2  in
        if uu____23721
        then
          let uu____23722 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23722
        else
          ((let uu____23725 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23725
            then
              let uu____23726 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____23727 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23726
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23727
            else ());
           (let uu____23729 =
              let uu____23734 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____23735 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____23734, uu____23735)  in
            match uu____23729 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23739),FStar_Syntax_Syntax.Total
                    (t2,uu____23741)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23758 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23758 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23761,FStar_Syntax_Syntax.Total uu____23762) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23780),FStar_Syntax_Syntax.Total
                    (t2,uu____23782)) ->
                     let uu____23799 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23799 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23803),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23805)) ->
                     let uu____23822 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23822 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23826),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23828)) ->
                     let uu____23845 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23845 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23848,FStar_Syntax_Syntax.Comp uu____23849) ->
                     let uu____23858 =
                       let uu___192_23863 = problem  in
                       let uu____23868 =
                         let uu____23869 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23869
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___192_23863.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23868;
                         FStar_TypeChecker_Common.relation =
                           (uu___192_23863.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___192_23863.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___192_23863.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___192_23863.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___192_23863.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___192_23863.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___192_23863.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___192_23863.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23858 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23870,FStar_Syntax_Syntax.Comp uu____23871) ->
                     let uu____23880 =
                       let uu___192_23885 = problem  in
                       let uu____23890 =
                         let uu____23891 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23891
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___192_23885.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23890;
                         FStar_TypeChecker_Common.relation =
                           (uu___192_23885.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___192_23885.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___192_23885.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___192_23885.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___192_23885.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___192_23885.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___192_23885.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___192_23885.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23880 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23892,FStar_Syntax_Syntax.GTotal uu____23893) ->
                     let uu____23902 =
                       let uu___193_23907 = problem  in
                       let uu____23912 =
                         let uu____23913 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23913
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___193_23907.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___193_23907.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___193_23907.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23912;
                         FStar_TypeChecker_Common.element =
                           (uu___193_23907.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___193_23907.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___193_23907.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___193_23907.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___193_23907.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___193_23907.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23902 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23914,FStar_Syntax_Syntax.Total uu____23915) ->
                     let uu____23924 =
                       let uu___193_23929 = problem  in
                       let uu____23934 =
                         let uu____23935 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23935
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___193_23929.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___193_23929.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___193_23929.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23934;
                         FStar_TypeChecker_Common.element =
                           (uu___193_23929.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___193_23929.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___193_23929.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___193_23929.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___193_23929.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___193_23929.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23924 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23936,FStar_Syntax_Syntax.Comp uu____23937) ->
                     let uu____23938 =
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
                     if uu____23938
                     then
                       let uu____23939 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____23939 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____23945 =
                            let uu____23950 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____23950
                            then (c1_comp, c2_comp)
                            else
                              (let uu____23956 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____23957 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____23956, uu____23957))
                             in
                          match uu____23945 with
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
                           (let uu____23964 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23964
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23966 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____23966 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23969 =
                                  let uu____23970 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____23971 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____23970 uu____23971
                                   in
                                giveup env uu____23969 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23978 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____24016  ->
              match uu____24016 with
              | (uu____24029,uu____24030,u,uu____24032,uu____24033,uu____24034)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23978 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24067 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24067 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24085 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24113  ->
                match uu____24113 with
                | (u1,u2) ->
                    let uu____24120 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24121 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24120 uu____24121))
         in
      FStar_All.pipe_right uu____24085 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24142,[])) -> "{}"
      | uu____24167 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24184 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____24184
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24187 =
              FStar_List.map
                (fun uu____24197  ->
                   match uu____24197 with
                   | (uu____24202,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24187 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24207 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24207 imps
  
let new_t_problem :
  'Auu____24222 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____24222 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____24222)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____24262 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____24262
                then
                  let uu____24263 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____24264 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24263
                    (rel_to_string rel) uu____24264
                else "TOP"  in
              let p = new_problem env lhs rel rhs elt loc reason  in p
  
let (new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____24296 =
              let uu____24299 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_74  -> FStar_Pervasives_Native.Some _0_74)
                uu____24299
               in
            FStar_Syntax_Syntax.new_bv uu____24296 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____24308 =
              let uu____24311 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_75  -> FStar_Pervasives_Native.Some _0_75)
                uu____24311
               in
            let uu____24314 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____24308 uu____24314  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____24350 = FStar_Options.eager_inference ()  in
          if uu____24350
          then
            let uu___194_24351 = probs  in
            {
              attempting = (uu___194_24351.attempting);
              wl_deferred = (uu___194_24351.wl_deferred);
              ctr = (uu___194_24351.ctr);
              defer_ok = false;
              smt_ok = (uu___194_24351.smt_ok);
              tcenv = (uu___194_24351.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____24362 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____24362
              then
                let uu____24363 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24363
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
          ((let uu____24381 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____24381
            then
              let uu____24382 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24382
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____24386 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____24386
             then
               let uu____24387 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24387
             else ());
            (let f2 =
               let uu____24390 =
                 let uu____24391 = FStar_Syntax_Util.unmeta f1  in
                 uu____24391.FStar_Syntax_Syntax.n  in
               match uu____24390 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24395 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___195_24396 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___195_24396.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___195_24396.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___195_24396.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____24421 =
              let uu____24422 =
                let uu____24423 =
                  let uu____24424 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____24424
                    (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24423;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____24422  in
            FStar_All.pipe_left
              (fun _0_77  -> FStar_Pervasives_Native.Some _0_77) uu____24421
  
let with_guard_no_simp :
  'Auu____24455 .
    'Auu____24455 ->
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
            let uu____24478 =
              let uu____24479 =
                let uu____24480 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____24480
                  (fun _0_78  -> FStar_TypeChecker_Common.NonTrivial _0_78)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24479;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24478
  
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
          (let uu____24526 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24526
           then
             let uu____24527 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24528 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24527
               uu____24528
           else ());
          (let prob =
             let uu____24531 =
               let uu____24536 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24536
                in
             FStar_All.pipe_left
               (fun _0_79  -> FStar_TypeChecker_Common.TProb _0_79)
               uu____24531
              in
           let g =
             let uu____24544 =
               let uu____24547 = singleton' env prob smt_ok  in
               solve_and_commit env uu____24547
                 (fun uu____24549  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____24544  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24573 = try_teq true env t1 t2  in
        match uu____24573 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____24577 = FStar_TypeChecker_Env.get_range env  in
              let uu____24578 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____24577 uu____24578);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24585 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____24585
              then
                let uu____24586 = FStar_Syntax_Print.term_to_string t1  in
                let uu____24587 = FStar_Syntax_Print.term_to_string t2  in
                let uu____24588 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24586
                  uu____24587 uu____24588
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
          let uu____24610 = FStar_TypeChecker_Env.get_range env  in
          let uu____24611 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____24610 uu____24611
  
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
        (let uu____24636 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24636
         then
           let uu____24637 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____24638 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____24637 uu____24638
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____24642 =
             let uu____24647 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24647 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_80  -> FStar_TypeChecker_Common.CProb _0_80) uu____24642
            in
         let uu____24652 =
           let uu____24655 = singleton env prob  in
           solve_and_commit env uu____24655
             (fun uu____24657  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____24652)
  
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
      fun uu____24692  ->
        match uu____24692 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24735 =
                 let uu____24740 =
                   let uu____24741 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____24742 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____24741 uu____24742
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____24740)  in
               let uu____24743 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____24735 uu____24743)
               in
            let equiv1 v1 v' =
              let uu____24755 =
                let uu____24760 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24761 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24760, uu____24761)  in
              match uu____24755 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24780 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24810 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24810 with
                      | FStar_Syntax_Syntax.U_unif uu____24817 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24846  ->
                                    match uu____24846 with
                                    | (u,v') ->
                                        let uu____24855 = equiv1 v1 v'  in
                                        if uu____24855
                                        then
                                          let uu____24858 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24858 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24874 -> []))
               in
            let uu____24879 =
              let wl =
                let uu___196_24883 = empty_worklist env  in
                {
                  attempting = (uu___196_24883.attempting);
                  wl_deferred = (uu___196_24883.wl_deferred);
                  ctr = (uu___196_24883.ctr);
                  defer_ok = false;
                  smt_ok = (uu___196_24883.smt_ok);
                  tcenv = (uu___196_24883.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24901  ->
                      match uu____24901 with
                      | (lb,v1) ->
                          let uu____24908 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24908 with
                           | USolved wl1 -> ()
                           | uu____24910 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24920 =
              match uu____24920 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24929) -> true
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
                      uu____24952,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24954,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24965) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24972,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24980 -> false)
               in
            let uu____24985 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25000  ->
                      match uu____25000 with
                      | (u,v1) ->
                          let uu____25007 = check_ineq (u, v1)  in
                          if uu____25007
                          then true
                          else
                            ((let uu____25010 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25010
                              then
                                let uu____25011 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25012 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25011
                                  uu____25012
                              else ());
                             false)))
               in
            if uu____24985
            then ()
            else
              ((let uu____25016 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25016
                then
                  ((let uu____25018 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25018);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25028 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25028))
                else ());
               (let uu____25038 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25038))
  
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
  
let rec (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let fail1 uu____25096 =
        match uu____25096 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____25110 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25110
       then
         let uu____25111 = wl_to_string wl  in
         let uu____25112 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____25111 uu____25112
       else ());
      (let g1 =
         let uu____25127 = solve_and_commit env wl fail1  in
         match uu____25127 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___197_25140 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___197_25140.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___197_25140.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___197_25140.FStar_TypeChecker_Env.implicits)
             }
         | uu____25145 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___198_25149 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___198_25149.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___198_25149.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___198_25149.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____25177 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25177 with
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
            let uu___199_25300 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___199_25300.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___199_25300.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___199_25300.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25301 =
            let uu____25302 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25302  in
          if uu____25301
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____25310 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____25311 =
                       let uu____25312 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____25312
                        in
                     FStar_Errors.diag uu____25310 uu____25311)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____25316 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____25317 =
                        let uu____25318 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____25318
                         in
                      FStar_Errors.diag uu____25316 uu____25317)
                   else ();
                   (let uu____25321 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____25321 "discharge_guard'"
                      env vc1);
                   (let uu____25322 = check_trivial vc1  in
                    match uu____25322 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____25329 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25330 =
                                let uu____25331 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____25331
                                 in
                              FStar_Errors.diag uu____25329 uu____25330)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____25336 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25337 =
                                let uu____25338 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____25338
                                 in
                              FStar_Errors.diag uu____25336 uu____25337)
                           else ();
                           (let vcs =
                              let uu____25349 = FStar_Options.use_tactics ()
                                 in
                              if uu____25349
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____25369  ->
                                     (let uu____25371 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____25371);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____25414  ->
                                              match uu____25414 with
                                              | (env1,goal,opts) ->
                                                  let uu____25430 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____25430, opts)))))
                              else
                                (let uu____25432 =
                                   let uu____25439 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____25439)  in
                                 [uu____25432])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25472  ->
                                    match uu____25472 with
                                    | (env1,goal,opts) ->
                                        let uu____25482 = check_trivial goal
                                           in
                                        (match uu____25482 with
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
                                                (let uu____25490 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25491 =
                                                   let uu____25492 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25493 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25492 uu____25493
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25490 uu____25491)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25496 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25497 =
                                                   let uu____25498 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25498
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25496 uu____25497)
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
      let uu____25512 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25512 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____25519 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____25519
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25530 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____25530 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (resolve_implicits' :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun forcelax  ->
      fun g  ->
        let unresolved u =
          let uu____25558 = FStar_Syntax_Unionfind.find u  in
          match uu____25558 with
          | FStar_Pervasives_Native.None  -> true
          | uu____25561 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____25583 = acc  in
          match uu____25583 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____25669 = hd1  in
                   (match uu____25669 with
                    | (uu____25682,env,u,tm,k,r) ->
                        let uu____25688 = unresolved u  in
                        if uu____25688
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___200_25718 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___200_25718.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___200_25718.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___200_25718.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___200_25718.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___200_25718.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___200_25718.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___200_25718.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___200_25718.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___200_25718.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___200_25718.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___200_25718.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___200_25718.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___200_25718.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___200_25718.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___200_25718.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___200_25718.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___200_25718.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___200_25718.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___200_25718.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___200_25718.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___200_25718.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___200_25718.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___200_25718.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___200_25718.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___200_25718.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___200_25718.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___200_25718.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___200_25718.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___200_25718.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___200_25718.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___200_25718.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___200_25718.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___200_25718.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___200_25718.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___200_25718.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___200_25718.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____25721 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____25721
                            then
                              let uu____25722 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____25723 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____25724 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____25722 uu____25723 uu____25724
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e when FStar_Errors.handleable e ->
                                  ((let uu____25735 =
                                      let uu____25744 =
                                        let uu____25751 =
                                          let uu____25752 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____25753 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____25752 uu____25753
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____25751, r)
                                         in
                                      [uu____25744]  in
                                    FStar_Errors.add_errors uu____25735);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___203_25767 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___203_25767.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___203_25767.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___203_25767.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____25770 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25777  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____25770 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                               in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1))))
           in
        let uu___204_25805 = g  in
        let uu____25806 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___204_25805.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___204_25805.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___204_25805.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25806
        }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____25868 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25868 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25881 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____25881
      | (reason,uu____25883,uu____25884,e,t,r)::uu____25888 ->
          let uu____25915 =
            let uu____25920 =
              let uu____25921 = FStar_Syntax_Print.term_to_string t  in
              let uu____25922 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25921 uu____25922
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25920)
             in
          FStar_Errors.raise_error uu____25915 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___205_25933 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___205_25933.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___205_25933.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___205_25933.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25960 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25960 with
      | FStar_Pervasives_Native.Some uu____25966 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25982 = try_teq false env t1 t2  in
        match uu____25982 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26008 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26008
         then
           let uu____26009 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26010 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26009
             uu____26010
         else ());
        (let uu____26012 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____26012 with
         | (prob,x) ->
             let g =
               let uu____26028 =
                 let uu____26031 = singleton' env prob true  in
                 solve_and_commit env uu____26031
                   (fun uu____26033  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26028  in
             ((let uu____26043 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26043
               then
                 let uu____26044 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26045 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26046 =
                   let uu____26047 = FStar_Util.must g  in
                   guard_to_string env uu____26047  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26044 uu____26045 uu____26046
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
        let uu____26081 = check_subtyping env t1 t2  in
        match uu____26081 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26100 =
              let uu____26101 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____26101 g  in
            FStar_Pervasives_Native.Some uu____26100
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26119 = check_subtyping env t1 t2  in
        match uu____26119 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26138 =
              let uu____26139 =
                let uu____26140 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26140]  in
              close_guard env uu____26139 g  in
            FStar_Pervasives_Native.Some uu____26138
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26157 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26157
         then
           let uu____26158 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26159 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26158
             uu____26159
         else ());
        (let uu____26161 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____26161 with
         | (prob,x) ->
             let g =
               let uu____26171 =
                 let uu____26174 = singleton' env prob false  in
                 solve_and_commit env uu____26174
                   (fun uu____26176  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26171  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26187 =
                      let uu____26188 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26188]  in
                    close_guard env uu____26187 g1  in
                  discharge_guard_nosmt env g2))
  