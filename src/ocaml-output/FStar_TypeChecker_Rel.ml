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
          [FStar_TypeChecker_Normalize.Primops;
          FStar_TypeChecker_Normalize.Beta;
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
          [FStar_TypeChecker_Normalize.Primops;
          FStar_TypeChecker_Normalize.Beta] env t
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
      let uu____3214 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3214 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3250 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3250, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3261 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3261 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3286 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3286 with
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
  fun uu____3367  ->
    match uu____3367 with
    | (t_base,refopt) ->
        let uu____3394 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3394 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3432 =
      let uu____3435 =
        let uu____3438 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3461  ->
                  match uu____3461 with | (uu____3468,uu____3469,x) -> x))
           in
        FStar_List.append wl.attempting uu____3438  in
      FStar_List.map (wl_prob_to_string wl) uu____3435  in
    FStar_All.pipe_right uu____3432 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3488 =
          let uu____3501 =
            let uu____3502 = FStar_Syntax_Subst.compress k  in
            uu____3502.FStar_Syntax_Syntax.n  in
          match uu____3501 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3555 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3555)
              else
                (let uu____3569 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3569 with
                 | (ys',t1,uu____3592) ->
                     let uu____3597 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3597))
          | uu____3638 ->
              let uu____3639 =
                let uu____3650 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3650)  in
              ((ys, t), uu____3639)
           in
        match uu____3488 with
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
                 let uu____3699 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3699 c  in
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
             let uu____3738 = p_guard prob  in
             match uu____3738 with
             | (uu____3743,uv) ->
                 ((let uu____3746 =
                     let uu____3747 = FStar_Syntax_Subst.compress uv  in
                     uu____3747.FStar_Syntax_Syntax.n  in
                   match uu____3746 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                       let bs = p_scope prob  in
                       let phi1 = u_abs k bs phi  in
                       ((let uu____3779 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3779
                         then
                           let uu____3780 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____3781 =
                             FStar_Syntax_Print.term_to_string uv  in
                           let uu____3782 =
                             FStar_Syntax_Print.term_to_string phi1  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3780
                             uu____3781 uu____3782
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3785 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___153_3788 = wl  in
                   {
                     attempting = (uu___153_3788.attempting);
                     wl_deferred = (uu___153_3788.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___153_3788.defer_ok);
                     smt_ok = (uu___153_3788.smt_ok);
                     tcenv = (uu___153_3788.tcenv)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3809 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3809
         then
           let uu____3810 = FStar_Util.string_of_int pid  in
           let uu____3811 =
             let uu____3812 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3812 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3810 uu____3811
         else ());
        commit sol;
        (let uu___154_3819 = wl  in
         {
           attempting = (uu___154_3819.attempting);
           wl_deferred = (uu___154_3819.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___154_3819.defer_ok);
           smt_ok = (uu___154_3819.smt_ok);
           tcenv = (uu___154_3819.tcenv)
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
             | (uu____3871,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3883 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____3883
              in
           (let uu____3889 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3889
            then
              let uu____3890 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3891 =
                let uu____3892 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3892 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3890 uu____3891
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
        let uu____3931 =
          let uu____3938 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3938 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3931
          (FStar_Util.for_some
             (fun uu____3974  ->
                match uu____3974 with
                | (uv,uu____3980) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3993 'Auu____3994 .
    'Auu____3993 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3994)
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
            let uu____4030 = occurs wl uk t  in Prims.op_Negation uu____4030
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____4037 =
                 let uu____4038 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____4039 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4038 uu____4039
                  in
               FStar_Pervasives_Native.Some uu____4037)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____4056 'Auu____4057 .
    'Auu____4056 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____4057)
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
            let uu____4116 = occurs_check env wl uk t  in
            match uu____4116 with
            | (occurs_ok,msg) ->
                let uu____4147 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____4147, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____4174 'Auu____4175 .
    (FStar_Syntax_Syntax.bv,'Auu____4174) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4175) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____4175) FStar_Pervasives_Native.tuple2
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
      let uu____4263 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4317  ->
                fun uu____4318  ->
                  match (uu____4317, uu____4318) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4399 =
                        let uu____4400 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4400  in
                      if uu____4399
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4425 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4425
                         then
                           let uu____4438 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____4438)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4263 with | (isect,uu____4479) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4508 'Auu____4509 .
    (FStar_Syntax_Syntax.bv,'Auu____4508) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4509) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4566  ->
              fun uu____4567  ->
                match (uu____4566, uu____4567) with
                | ((a,uu____4585),(b,uu____4587)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4606 'Auu____4607 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4606) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4607)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4607)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4661 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4675  ->
                      match uu____4675 with
                      | (b,uu____4681) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4661
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4697 -> FStar_Pervasives_Native.None
  
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
            let uu____4776 = pat_var_opt env seen hd1  in
            (match uu____4776 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4790 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4790
                   then
                     let uu____4791 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4791
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4811 =
      let uu____4812 = FStar_Syntax_Subst.compress t  in
      uu____4812.FStar_Syntax_Syntax.n  in
    match uu____4811 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4815 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4832;
           FStar_Syntax_Syntax.pos = uu____4833;
           FStar_Syntax_Syntax.vars = uu____4834;_},uu____4835)
        -> true
    | uu____4872 -> false
  
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
           FStar_Syntax_Syntax.pos = uu____4998;
           FStar_Syntax_Syntax.vars = uu____4999;_},args)
        -> (t, uv, k, args)
    | uu____5067 -> failwith "Not a flex-uvar"
  
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
      let uu____5148 = destruct_flex_t t  in
      match uu____5148 with
      | (t1,uv,k,args) ->
          let uu____5263 = pat_vars env [] args  in
          (match uu____5263 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____5361 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5450 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____5488 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5501 -> false
  
let string_of_option :
  'Auu____5508 .
    ('Auu____5508 -> Prims.string) ->
      'Auu____5508 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___127_5523  ->
      match uu___127_5523 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5529 = f x  in Prims.strcat "Some " uu____5529
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___128_5534  ->
    match uu___128_5534 with
    | MisMatch (d1,d2) ->
        let uu____5545 =
          let uu____5546 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5547 =
            let uu____5548 =
              let uu____5549 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5549 ")"  in
            Prims.strcat ") (" uu____5548  in
          Prims.strcat uu____5546 uu____5547  in
        Prims.strcat "MisMatch (" uu____5545
    | HeadMatch u ->
        let uu____5551 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____5551
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___129_5556  ->
    match uu___129_5556 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____5571 -> HeadMatch false
  
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
          let uu____5585 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5585 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5596 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5619 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5628 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5656 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5656
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5657 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5658 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5659 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5676 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5689 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5713) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5719,uu____5720) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5762) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5783;
             FStar_Syntax_Syntax.index = uu____5784;
             FStar_Syntax_Syntax.sort = t2;_},uu____5786)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5793 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5794 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5795 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5808 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5815 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5833 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5833
  
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
            let uu____5860 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5860
            then FullMatch
            else
              (let uu____5862 =
                 let uu____5871 =
                   let uu____5874 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5874  in
                 let uu____5875 =
                   let uu____5878 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5878  in
                 (uu____5871, uu____5875)  in
               MisMatch uu____5862)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5884),FStar_Syntax_Syntax.Tm_uinst (g,uu____5886)) ->
            let uu____5895 = head_matches env f g  in
            FStar_All.pipe_right uu____5895 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5898 = FStar_Const.eq_const c d  in
            if uu____5898
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5905),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5907)) ->
            let uu____5956 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5956
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5963),FStar_Syntax_Syntax.Tm_refine (y,uu____5965)) ->
            let uu____5974 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5974 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5976),uu____5977) ->
            let uu____5982 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5982 head_match
        | (uu____5983,FStar_Syntax_Syntax.Tm_refine (x,uu____5985)) ->
            let uu____5990 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5990 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5991,FStar_Syntax_Syntax.Tm_type
           uu____5992) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5993,FStar_Syntax_Syntax.Tm_arrow uu____5994) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6020),FStar_Syntax_Syntax.Tm_app (head',uu____6022))
            ->
            let uu____6063 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6063 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6065),uu____6066) ->
            let uu____6087 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6087 head_match
        | (uu____6088,FStar_Syntax_Syntax.Tm_app (head1,uu____6090)) ->
            let uu____6111 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6111 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6112,FStar_Syntax_Syntax.Tm_let
           uu____6113) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6138,FStar_Syntax_Syntax.Tm_match uu____6139) ->
            HeadMatch true
        | uu____6184 ->
            let uu____6189 =
              let uu____6198 = delta_depth_of_term env t11  in
              let uu____6201 = delta_depth_of_term env t21  in
              (uu____6198, uu____6201)  in
            MisMatch uu____6189
  
let head_matches_delta :
  'Auu____6218 .
    FStar_TypeChecker_Env.env ->
      'Auu____6218 ->
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
            let uu____6257 = FStar_Syntax_Util.head_and_args t  in
            match uu____6257 with
            | (head1,uu____6275) ->
                let uu____6296 =
                  let uu____6297 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6297.FStar_Syntax_Syntax.n  in
                (match uu____6296 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6303 =
                       FStar_TypeChecker_Env.lookup_definition
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant;
                         FStar_TypeChecker_Env.Eager_unfolding_only] env
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (match uu____6303 with
                      | FStar_Pervasives_Native.None  ->
                          ((let uu____6317 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelDelta")
                               in
                            if uu____6317
                            then
                              let uu____6318 =
                                FStar_Syntax_Print.term_to_string head1  in
                              FStar_Util.print1
                                "No definition found for %s\n" uu____6318
                            else ());
                           FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some uu____6320 ->
                          let t' =
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF;
                              FStar_TypeChecker_Normalize.Primops;
                              FStar_TypeChecker_Normalize.Beta;
                              FStar_TypeChecker_Normalize.Eager_unfolding]
                              env t
                             in
                          ((let uu____6331 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelDelta")
                               in
                            if uu____6331
                            then
                              let uu____6332 =
                                FStar_Syntax_Print.term_to_string t  in
                              let uu____6333 =
                                FStar_Syntax_Print.term_to_string t'  in
                              FStar_Util.print2 "Inlined %s to %s\n"
                                uu____6332 uu____6333
                            else ());
                           FStar_Pervasives_Native.Some t'))
                 | uu____6335 -> FStar_Pervasives_Native.None)
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
            (let uu____6473 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6473
             then
               let uu____6474 = FStar_Syntax_Print.term_to_string t11  in
               let uu____6475 = FStar_Syntax_Print.term_to_string t21  in
               let uu____6476 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6474
                 uu____6475 uu____6476
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____6500 =
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
               match uu____6500 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____6545 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____6545 with
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
                  uu____6577),uu____6578)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6596 =
                      let uu____6605 = maybe_inline t11  in
                      let uu____6608 = maybe_inline t21  in
                      (uu____6605, uu____6608)  in
                    match uu____6596 with
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
                 (uu____6645,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____6646))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6664 =
                      let uu____6673 = maybe_inline t11  in
                      let uu____6676 = maybe_inline t21  in
                      (uu____6673, uu____6676)  in
                    match uu____6664 with
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
             | MisMatch uu____6725 -> fail1 n_delta r t11 t21
             | uu____6734 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6747 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6747
           then
             let uu____6748 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6749 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6750 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6757 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6775 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6775
                    (fun uu____6809  ->
                       match uu____6809 with
                       | (t11,t21) ->
                           let uu____6816 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6817 =
                             let uu____6818 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6818  in
                           Prims.strcat uu____6816 uu____6817))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____6748 uu____6749 uu____6750 uu____6757
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp 
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6858 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6902 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let (tc_to_string : tc -> Prims.string) =
  fun uu___130_6916  ->
    match uu___130_6916 with
    | T (t,uu____6918) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6942 = FStar_Syntax_Util.type_u ()  in
      match uu____6942 with
      | (t,uu____6948) ->
          let uu____6949 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6949
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6964 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6964 FStar_Pervasives_Native.fst
  
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
        let uu____7038 = head_matches env t1 t'  in
        match uu____7038 with
        | MisMatch uu____7039 -> false
        | uu____7048 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____7148,imp),T (t2,uu____7151)) -> (t2, imp)
                     | uu____7174 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7241  ->
                    match uu____7241 with
                    | (t2,uu____7255) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7302 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7302 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7387))::tcs2) ->
                       aux
                         (((let uu___155_7426 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_7426.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_7426.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7444 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___131_7501 =
                 match uu___131_7501 with
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
               let uu____7620 = decompose1 [] bs1  in
               (rebuild, matches, uu____7620))
      | uu____7671 ->
          let rebuild uu___132_7679 =
            match uu___132_7679 with
            | [] -> t1
            | uu____7682 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___133_7717  ->
    match uu___133_7717 with
    | T (t,uu____7719) -> t
    | uu____7732 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___134_7737  ->
    match uu___134_7737 with
    | T (t,uu____7739) -> FStar_Syntax_Syntax.as_arg t
    | uu____7752 -> failwith "Impossible"
  
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
              | (uu____7884,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7913 = new_uvar r scope1 k  in
                  (match uu____7913 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7931 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7948 =
                         let uu____7949 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_21  ->
                              FStar_TypeChecker_Common.TProb _0_21)
                           uu____7949
                          in
                       ((T (gi_xs, mk_kind)), uu____7948))
              | (uu____7964,uu____7965,C uu____7966) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____8119 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8136;
                         FStar_Syntax_Syntax.vars = uu____8137;_})
                        ->
                        let uu____8160 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8160 with
                         | (T (gi_xs,uu____8186),prob) ->
                             let uu____8200 =
                               let uu____8201 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_22  -> C _0_22)
                                 uu____8201
                                in
                             (uu____8200, [prob])
                         | uu____8204 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8219;
                         FStar_Syntax_Syntax.vars = uu____8220;_})
                        ->
                        let uu____8243 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8243 with
                         | (T (gi_xs,uu____8269),prob) ->
                             let uu____8283 =
                               let uu____8284 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_23  -> C _0_23)
                                 uu____8284
                                in
                             (uu____8283, [prob])
                         | uu____8287 -> failwith "impossible")
                    | (uu____8298,uu____8299,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8301;
                         FStar_Syntax_Syntax.vars = uu____8302;_})
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
                        let uu____8437 =
                          let uu____8446 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8446 FStar_List.unzip
                           in
                        (match uu____8437 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8500 =
                                 let uu____8501 =
                                   let uu____8504 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8504 un_T  in
                                 let uu____8505 =
                                   let uu____8514 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8514
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8501;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8505;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8500
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8523 ->
                        let uu____8536 = sub_prob scope1 args q  in
                        (match uu____8536 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____8119 with
                   | (tc,probs) ->
                       let uu____8567 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8630,uu____8631),T
                            (t,uu____8633)) ->
                             let b1 =
                               ((let uu___156_8674 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___156_8674.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___156_8674.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8675 =
                               let uu____8682 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8682 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8675)
                         | uu____8717 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8567 with
                        | (bopt,scope2,args1) ->
                            let uu____8801 = aux scope2 args1 qs2  in
                            (match uu____8801 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8839 =
                                           let uu____8842 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8842  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8839
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
                                         let uu____8867 =
                                           let uu____8870 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8871 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8870 :: uu____8871  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8867
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
  'Auu____8945 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8945)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8945)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___157_8968 = p  in
      let uu____8973 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8974 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___157_8968.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8973;
        FStar_TypeChecker_Common.relation =
          (uu___157_8968.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8974;
        FStar_TypeChecker_Common.element =
          (uu___157_8968.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___157_8968.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___157_8968.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___157_8968.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___157_8968.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___157_8968.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8990 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8990
            (fun _0_24  -> FStar_TypeChecker_Common.TProb _0_24)
      | FStar_TypeChecker_Common.CProb uu____8999 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____9023 = compress_prob wl pr  in
        FStar_All.pipe_right uu____9023 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9033 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9033 with
           | (lh,uu____9053) ->
               let uu____9074 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9074 with
                | (rh,uu____9094) ->
                    let uu____9115 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9132,FStar_Syntax_Syntax.Tm_uvar uu____9133)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9170,uu____9171)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9192,FStar_Syntax_Syntax.Tm_uvar uu____9193)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9214,uu____9215)
                          ->
                          let uu____9232 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9232 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9281 ->
                                    let rank =
                                      let uu____9289 = is_top_level_prob prob
                                         in
                                      if uu____9289
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9291 =
                                      let uu___158_9296 = tp  in
                                      let uu____9301 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___158_9296.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___158_9296.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___158_9296.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9301;
                                        FStar_TypeChecker_Common.element =
                                          (uu___158_9296.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___158_9296.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___158_9296.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___158_9296.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___158_9296.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___158_9296.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9291)))
                      | (uu____9312,FStar_Syntax_Syntax.Tm_uvar uu____9313)
                          ->
                          let uu____9330 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9330 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9379 ->
                                    let uu____9386 =
                                      let uu___159_9393 = tp  in
                                      let uu____9398 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___159_9393.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9398;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___159_9393.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___159_9393.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___159_9393.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___159_9393.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___159_9393.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___159_9393.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___159_9393.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___159_9393.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9386)))
                      | (uu____9415,uu____9416) -> (rigid_rigid, tp)  in
                    (match uu____9115 with
                     | (rank,tp1) ->
                         let uu____9435 =
                           FStar_All.pipe_right
                             (let uu___160_9441 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___160_9441.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___160_9441.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___160_9441.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___160_9441.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___160_9441.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___160_9441.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___160_9441.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___160_9441.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___160_9441.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_25  ->
                                FStar_TypeChecker_Common.TProb _0_25)
                            in
                         (rank, uu____9435))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9451 =
            FStar_All.pipe_right
              (let uu___161_9457 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___161_9457.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___161_9457.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___161_9457.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___161_9457.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___161_9457.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___161_9457.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___161_9457.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___161_9457.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___161_9457.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_26  -> FStar_TypeChecker_Common.CProb _0_26)
             in
          (rigid_rigid, uu____9451)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9518 probs =
      match uu____9518 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9571 = rank wl hd1  in
               (match uu____9571 with
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
    match projectee with | UDeferred _0 -> true | uu____9687 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9701 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9715 -> false
  
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
                        let uu____9767 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9767 with
                        | (k,uu____9773) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9783 -> false)))
            | uu____9784 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9836 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9842 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9842 = (Prims.parse_int "0")))
                           in
                        if uu____9836 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9858 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9864 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9864 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9858)
               in
            let uu____9865 = filter1 u12  in
            let uu____9868 = filter1 u22  in (uu____9865, uu____9868)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9897 = filter_out_common_univs us1 us2  in
                (match uu____9897 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9956 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9956 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9959 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9969 =
                          let uu____9970 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9971 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9970
                            uu____9971
                           in
                        UFailed uu____9969))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9995 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9995 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____10021 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____10021 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____10024 ->
                let uu____10029 =
                  let uu____10030 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____10031 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____10030
                    uu____10031 msg
                   in
                UFailed uu____10029
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10032,uu____10033) ->
              let uu____10034 =
                let uu____10035 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10036 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10035 uu____10036
                 in
              failwith uu____10034
          | (FStar_Syntax_Syntax.U_unknown ,uu____10037) ->
              let uu____10038 =
                let uu____10039 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10040 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10039 uu____10040
                 in
              failwith uu____10038
          | (uu____10041,FStar_Syntax_Syntax.U_bvar uu____10042) ->
              let uu____10043 =
                let uu____10044 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10045 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10044 uu____10045
                 in
              failwith uu____10043
          | (uu____10046,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10047 =
                let uu____10048 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10049 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10048 uu____10049
                 in
              failwith uu____10047
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10073 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10073
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10095 = occurs_univ v1 u3  in
              if uu____10095
              then
                let uu____10096 =
                  let uu____10097 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10098 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10097 uu____10098
                   in
                try_umax_components u11 u21 uu____10096
              else
                (let uu____10100 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10100)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10120 = occurs_univ v1 u3  in
              if uu____10120
              then
                let uu____10121 =
                  let uu____10122 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10123 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10122 uu____10123
                   in
                try_umax_components u11 u21 uu____10121
              else
                (let uu____10125 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10125)
          | (FStar_Syntax_Syntax.U_max uu____10134,uu____10135) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10141 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10141
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10143,FStar_Syntax_Syntax.U_max uu____10144) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10150 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10150
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10152,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10153,FStar_Syntax_Syntax.U_name uu____10154) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10155) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10156) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10157,FStar_Syntax_Syntax.U_succ uu____10158) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10159,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10259 = bc1  in
      match uu____10259 with
      | (bs1,mk_cod1) ->
          let uu____10303 = bc2  in
          (match uu____10303 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10414 = aux xs ys  in
                     (match uu____10414 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10497 =
                       let uu____10504 = mk_cod1 xs  in ([], uu____10504)  in
                     let uu____10507 =
                       let uu____10514 = mk_cod2 ys  in ([], uu____10514)  in
                     (uu____10497, uu____10507)
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
                let uu____10571 =
                  let uu____10572 = FStar_Syntax_Syntax.bv_to_name x  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10572 t21  in
                FStar_Syntax_Util.mk_forall u_x x uu____10571
             in
          match problem.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ  ->
              let uu____10575 =
                mk_eq2 (FStar_TypeChecker_Common.TProb problem) t1 t2  in
              FStar_All.pipe_left
                (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                uu____10575
          | FStar_TypeChecker_Common.SUB  ->
              let uu____10578 = has_type_guard t1 t2  in
              FStar_All.pipe_left
                (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                uu____10578
          | FStar_TypeChecker_Common.SUBINV  ->
              let uu____10589 = has_type_guard t2 t1  in
              FStar_All.pipe_left
                (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                uu____10589
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10770 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10770
       then
         let uu____10771 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10771
       else ());
      (let uu____10773 = next_prob probs  in
       match uu____10773 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___162_10794 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___162_10794.wl_deferred);
               ctr = (uu___162_10794.ctr);
               defer_ok = (uu___162_10794.defer_ok);
               smt_ok = (uu___162_10794.smt_ok);
               tcenv = (uu___162_10794.tcenv)
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
                  let uu____10805 = solve_flex_rigid_join env tp probs1  in
                  (match uu____10805 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10810 = solve_rigid_flex_meet env tp probs1
                        in
                     match uu____10810 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10815,uu____10816) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10833 ->
                let uu____10842 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10901  ->
                          match uu____10901 with
                          | (c,uu____10909,uu____10910) -> c < probs.ctr))
                   in
                (match uu____10842 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10951 =
                            FStar_List.map
                              (fun uu____10966  ->
                                 match uu____10966 with
                                 | (uu____10977,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10951
                      | uu____10980 ->
                          let uu____10989 =
                            let uu___163_10990 = probs  in
                            let uu____10991 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11012  ->
                                      match uu____11012 with
                                      | (uu____11019,uu____11020,y) -> y))
                               in
                            {
                              attempting = uu____10991;
                              wl_deferred = rest;
                              ctr = (uu___163_10990.ctr);
                              defer_ok = (uu___163_10990.defer_ok);
                              smt_ok = (uu___163_10990.smt_ok);
                              tcenv = (uu___163_10990.tcenv)
                            }  in
                          solve env uu____10989))))

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
            let uu____11027 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11027 with
            | USolved wl1 ->
                let uu____11029 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11029
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
                  let uu____11081 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11081 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11084 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11096;
                  FStar_Syntax_Syntax.vars = uu____11097;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11100;
                  FStar_Syntax_Syntax.vars = uu____11101;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11113,uu____11114) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11121,FStar_Syntax_Syntax.Tm_uinst uu____11122) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11129 -> USolved wl

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
            ((let uu____11139 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11139
              then
                let uu____11140 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11140 msg
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
        (let uu____11149 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11149
         then
           let uu____11150 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____11150
         else ());
        (let uu____11152 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____11152 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____11218 = head_matches_delta env () t1 t2  in
               match uu____11218 with
               | (mr,ts) ->
                   (match mr with
                    | HeadMatch (true ) -> FStar_Pervasives_Native.None
                    | MisMatch uu____11265 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch (false ) ->
                        let uu____11314 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____11329 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____11330 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____11329, uu____11330)
                          | FStar_Pervasives_Native.None  ->
                              let uu____11335 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____11336 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____11335, uu____11336)
                           in
                        (match uu____11314 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11366 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_30  ->
                                    FStar_TypeChecker_Common.TProb _0_30)
                                 uu____11366
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11397 =
                                    let uu____11406 =
                                      let uu____11409 =
                                        let uu____11416 =
                                          let uu____11417 =
                                            let uu____11424 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____11424)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11417
                                           in
                                        FStar_Syntax_Syntax.mk uu____11416
                                         in
                                      uu____11409
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____11432 =
                                      let uu____11435 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____11435]  in
                                    (uu____11406, uu____11432)  in
                                  FStar_Pervasives_Native.Some uu____11397
                              | (uu____11448,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11450)) ->
                                  let uu____11455 =
                                    let uu____11462 =
                                      let uu____11465 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____11465]  in
                                    (t11, uu____11462)  in
                                  FStar_Pervasives_Native.Some uu____11455
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11475),uu____11476) ->
                                  let uu____11481 =
                                    let uu____11488 =
                                      let uu____11491 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____11491]  in
                                    (t21, uu____11488)  in
                                  FStar_Pervasives_Native.Some uu____11481
                              | uu____11500 ->
                                  let uu____11505 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____11505 with
                                   | (head1,uu____11529) ->
                                       let uu____11550 =
                                         let uu____11551 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____11551.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____11550 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11562;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11564;_}
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
                                        | uu____11571 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11584) ->
                  let uu____11609 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___135_11635  ->
                            match uu___135_11635 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11642 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____11642 with
                                      | (u',uu____11658) ->
                                          let uu____11679 =
                                            let uu____11680 = whnf env u'  in
                                            uu____11680.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11679 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11684) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11709 -> false))
                                 | uu____11710 -> false)
                            | uu____11713 -> false))
                     in
                  (match uu____11609 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11751 tps =
                         match uu____11751 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11799 =
                                    let uu____11808 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____11808  in
                                  (match uu____11799 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11843 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11852 =
                         let uu____11861 =
                           let uu____11868 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11868, [])  in
                         make_lower_bound uu____11861 lower_bounds  in
                       (match uu____11852 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11880 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11880
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
                            ((let uu____11900 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11900
                              then
                                let wl' =
                                  let uu___164_11902 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___164_11902.wl_deferred);
                                    ctr = (uu___164_11902.ctr);
                                    defer_ok = (uu___164_11902.defer_ok);
                                    smt_ok = (uu___164_11902.smt_ok);
                                    tcenv = (uu___164_11902.tcenv)
                                  }  in
                                let uu____11903 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11903
                              else ());
                             (let uu____11905 =
                                solve_t env eq_prob
                                  (let uu___165_11907 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___165_11907.wl_deferred);
                                     ctr = (uu___165_11907.ctr);
                                     defer_ok = (uu___165_11907.defer_ok);
                                     smt_ok = (uu___165_11907.smt_ok);
                                     tcenv = (uu___165_11907.tcenv)
                                   })
                                 in
                              match uu____11905 with
                              | Success uu____11910 ->
                                  let wl1 =
                                    let uu___166_11912 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___166_11912.wl_deferred);
                                      ctr = (uu___166_11912.ctr);
                                      defer_ok = (uu___166_11912.defer_ok);
                                      smt_ok = (uu___166_11912.smt_ok);
                                      tcenv = (uu___166_11912.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11914 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11919 -> FStar_Pervasives_Native.None))))
              | uu____11920 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11929 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11929
         then
           let uu____11930 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11930
         else ());
        (let uu____11932 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11932 with
         | (u,args) ->
             let uu____11971 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11971 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____12020 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____12020 with
                    | (h1,args1) ->
                        let uu____12061 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____12061 with
                         | (h2,uu____12081) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____12108 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____12108
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____12126 =
                                          let uu____12129 =
                                            let uu____12130 =
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
                                                   _0_31) uu____12130
                                             in
                                          [uu____12129]  in
                                        FStar_Pervasives_Native.Some
                                          uu____12126))
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
                                       (let uu____12163 =
                                          let uu____12166 =
                                            let uu____12167 =
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
                                                   _0_32) uu____12167
                                             in
                                          [uu____12166]  in
                                        FStar_Pervasives_Native.Some
                                          uu____12163))
                                  else FStar_Pervasives_Native.None
                              | uu____12181 -> FStar_Pervasives_Native.None))
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
                             let uu____12275 =
                               let uu____12284 =
                                 let uu____12287 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____12287  in
                               (uu____12284, m1)  in
                             FStar_Pervasives_Native.Some uu____12275)
                    | (uu____12300,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12302)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12350),uu____12351) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12398 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12451) ->
                       let uu____12476 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___136_12502  ->
                                 match uu___136_12502 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12509 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____12509 with
                                           | (u',uu____12525) ->
                                               let uu____12546 =
                                                 let uu____12547 =
                                                   whnf env u'  in
                                                 uu____12547.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____12546 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12551) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12576 -> false))
                                      | uu____12577 -> false)
                                 | uu____12580 -> false))
                          in
                       (match uu____12476 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12622 tps =
                              match uu____12622 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12684 =
                                         let uu____12695 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____12695  in
                                       (match uu____12684 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12746 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____12757 =
                              let uu____12768 =
                                let uu____12777 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____12777, [])  in
                              make_upper_bound uu____12768 upper_bounds  in
                            (match uu____12757 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12791 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12791
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
                                 ((let uu____12817 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12817
                                   then
                                     let wl' =
                                       let uu___167_12819 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___167_12819.wl_deferred);
                                         ctr = (uu___167_12819.ctr);
                                         defer_ok = (uu___167_12819.defer_ok);
                                         smt_ok = (uu___167_12819.smt_ok);
                                         tcenv = (uu___167_12819.tcenv)
                                       }  in
                                     let uu____12820 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12820
                                   else ());
                                  (let uu____12822 =
                                     solve_t env eq_prob
                                       (let uu___168_12824 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___168_12824.wl_deferred);
                                          ctr = (uu___168_12824.ctr);
                                          defer_ok =
                                            (uu___168_12824.defer_ok);
                                          smt_ok = (uu___168_12824.smt_ok);
                                          tcenv = (uu___168_12824.tcenv)
                                        })
                                      in
                                   match uu____12822 with
                                   | Success uu____12827 ->
                                       let wl1 =
                                         let uu___169_12829 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___169_12829.wl_deferred);
                                           ctr = (uu___169_12829.ctr);
                                           defer_ok =
                                             (uu___169_12829.defer_ok);
                                           smt_ok = (uu___169_12829.smt_ok);
                                           tcenv = (uu___169_12829.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____12831 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12836 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12837 -> failwith "Impossible: Not a flex-rigid")))

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
              (let uu____12855 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12855
               then
                 let uu____12856 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12857 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12856 (rel_to_string (p_rel orig)) uu____12857
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____12927 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____12927
                       then
                         let uu____12928 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____12928
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___170_12982 = hd1  in
                       let uu____12983 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___170_12982.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___170_12982.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12983
                       }  in
                     let hd21 =
                       let uu___171_12987 = hd2  in
                       let uu____12988 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___171_12987.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___171_12987.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12988
                       }  in
                     let prob =
                       let uu____12992 =
                         let uu____12997 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____12997 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33)
                         uu____12992
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____13008 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____13008
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____13012 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____13012 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____13050 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____13055 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____13050 uu____13055
                             in
                          ((let uu____13065 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13065
                            then
                              let uu____13066 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____13067 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____13066 uu____13067
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____13090 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____13100 = aux scope env [] bs1 bs2  in
               match uu____13100 with
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
        (let uu____13125 = compress_tprob wl problem  in
         solve_t' env uu____13125 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____13173 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____13173
            then
              let uu____13174 = FStar_Syntax_Print.term_to_string t1  in
              let uu____13175 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____13176 = FStar_Syntax_Print.term_to_string t2  in
              let uu____13177 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____13174 uu____13175 uu____13176 uu____13177
            else ());
           (let uu____13180 = FStar_Syntax_Util.head_and_args t1  in
            match uu____13180 with
            | (head1,args1) ->
                let uu____13217 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____13217 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____13271 =
                         let uu____13272 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13273 = args_to_string args1  in
                         let uu____13274 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____13275 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____13272 uu____13273 uu____13274 uu____13275
                          in
                       giveup env1 uu____13271 orig
                     else
                       (let uu____13277 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____13283 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____13283 = FStar_Syntax_Util.Equal)
                           in
                        if uu____13277
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___172_13285 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___172_13285.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___172_13285.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___172_13285.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___172_13285.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___172_13285.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___172_13285.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___172_13285.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___172_13285.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____13289 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____13289 with
                              | USolved wl2 ->
                                  let uu____13291 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____13291
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____13295 = base_and_refinement env1 t1  in
                           match uu____13295 with
                           | (base1,refinement1) ->
                               let uu____13320 = base_and_refinement env1 t2
                                  in
                               (match uu____13320 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         if need_unif
                                         then
                                           let subprobs =
                                             FStar_List.map2
                                               (fun uu____13399  ->
                                                  fun uu____13400  ->
                                                    match (uu____13399,
                                                            uu____13400)
                                                    with
                                                    | ((a,uu____13426),
                                                       (a',uu____13428)) ->
                                                        let uu____13449 =
                                                          let uu____13454 =
                                                            p_scope orig  in
                                                          mk_problem
                                                            uu____13454 orig
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
                                                          uu____13449)
                                               ((head1,
                                                  FStar_Pervasives_Native.None)
                                               :: args1)
                                               ((head2,
                                                  FStar_Pervasives_Native.None)
                                               :: args2)
                                              in
                                           ((let uu____13484 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel")
                                                in
                                             if uu____13484
                                             then
                                               let uu____13485 =
                                                 FStar_Syntax_Print.list_to_string
                                                   (prob_to_string env1)
                                                   subprobs
                                                  in
                                               FStar_Util.print1
                                                 "Adding subproblems for arguments: %s"
                                                 uu____13485
                                             else ());
                                            (let formula =
                                               let uu____13488 =
                                                 FStar_List.map
                                                   (fun p  ->
                                                      FStar_Pervasives_Native.fst
                                                        (p_guard p)) subprobs
                                                  in
                                               FStar_Syntax_Util.mk_conj_l
                                                 uu____13488
                                                in
                                             let wl2 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    formula) [] wl1
                                                in
                                             solve env1
                                               (attempt subprobs wl2)))
                                         else
                                           (let uu____13495 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____13495 with
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
                                                    (fun uu____13517  ->
                                                       fun uu____13518  ->
                                                         match (uu____13517,
                                                                 uu____13518)
                                                         with
                                                         | ((a,uu____13536),
                                                            (a',uu____13538))
                                                             ->
                                                             let uu____13547
                                                               =
                                                               let uu____13552
                                                                 =
                                                                 p_scope orig
                                                                  in
                                                               mk_problem
                                                                 uu____13552
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
                                                               uu____13547)
                                                    args1 args2
                                                   in
                                                ((let uu____13558 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____13558
                                                  then
                                                    let uu____13559 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____13559
                                                  else ());
                                                 (let formula =
                                                    let uu____13562 =
                                                      FStar_List.map
                                                        (fun p  ->
                                                           FStar_Pervasives_Native.fst
                                                             (p_guard p))
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____13562
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  solve env1
                                                    (attempt subprobs wl3))))
                                     | uu____13568 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___173_13604 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___173_13604.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___173_13604.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___173_13604.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___173_13604.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.scope
                                                =
                                                (uu___173_13604.FStar_TypeChecker_Common.scope);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___173_13604.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___173_13604.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___173_13604.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____13644 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____13644
            then
              let uu____13645 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____13646 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____13647 = FStar_Syntax_Print.term_to_string t1  in
              let uu____13648 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____13645 uu____13646 uu____13647 uu____13648
            else ());
           (let uu____13650 = head_matches_delta env1 wl1 t1 t2  in
            match uu____13650 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____13681,uu____13682) ->
                     let rec may_relate head3 =
                       let uu____13709 =
                         let uu____13710 = FStar_Syntax_Subst.compress head3
                            in
                         uu____13710.FStar_Syntax_Syntax.n  in
                       match uu____13709 with
                       | FStar_Syntax_Syntax.Tm_name uu____13713 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____13714 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____13737;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____13738;
                             FStar_Syntax_Syntax.fv_qual = uu____13739;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____13742;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____13743;
                             FStar_Syntax_Syntax.fv_qual = uu____13744;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____13748,uu____13749) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____13791) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____13797) ->
                           may_relate t
                       | uu____13802 -> false  in
                     let uu____13803 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____13803
                     then
                       let guard = guard_of_prob env1 problem t1 t2  in
                       let uu____13807 = solve_prob orig guard [] wl1  in
                       solve env1 uu____13807
                     else
                       (let uu____13809 =
                          let uu____13810 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____13811 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____13810 uu____13811
                           in
                        giveup env1 uu____13809 orig)
                 | (HeadMatch uu____13812,FStar_Pervasives_Native.Some
                    (t11,t21)) ->
                     solve_t env1
                       (let uu___174_13826 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___174_13826.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___174_13826.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___174_13826.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___174_13826.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___174_13826.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___174_13826.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___174_13826.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___174_13826.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___174_13840 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___174_13840.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___174_13840.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___174_13840.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___174_13840.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___174_13840.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___174_13840.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___174_13840.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___174_13840.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let force_quasi_pattern xs_opt uu____13896 =
           match uu____13896 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____13940 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____13940 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____14052  ->
                      let uu____14053 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____14053);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____14121  ->
                                match uu____14121 with
                                | (x,imp) ->
                                    let uu____14132 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____14132, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____14145 = FStar_Syntax_Util.type_u ()  in
                        match uu____14145 with
                        | (t1,uu____14151) ->
                            let uu____14152 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____14152
                         in
                      let uu____14157 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____14157 with
                       | (t',tm_u1) ->
                           let uu____14170 = destruct_flex_t t'  in
                           (match uu____14170 with
                            | (uu____14207,u1,k1,uu____14210) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____14269 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____14269
                                   in
                                let sol =
                                  let uu____14273 =
                                    let uu____14282 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____14282)  in
                                  TERM uu____14273  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____14417  ->
                            let uu____14418 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____14419 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____14418 uu____14419);
                       (let uu____14432 = pat_var_opt env pat_args hd1  in
                        match uu____14432 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____14452  ->
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
                                       (fun uu____14495  ->
                                          match uu____14495 with
                                          | (x,uu____14501) ->
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
                                 (fun uu____14516  ->
                                    let uu____14517 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____14530 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____14517
                                      uu____14530);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____14534 =
                                  let uu____14535 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____14535  in
                                if uu____14534
                                then
                                  (debug1
                                     (fun uu____14547  ->
                                        let uu____14548 =
                                          let uu____14551 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____14564 =
                                            let uu____14567 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____14568 =
                                              let uu____14571 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____14572 =
                                                let uu____14575 =
                                                  names_to_string fvs  in
                                                let uu____14576 =
                                                  let uu____14579 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____14579]  in
                                                uu____14575 :: uu____14576
                                                 in
                                              uu____14571 :: uu____14572  in
                                            uu____14567 :: uu____14568  in
                                          uu____14551 :: uu____14564  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____14548);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____14581 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____14584 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____14581 (formal ::
                                     pattern_vars) uu____14584 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____14591::uu____14592) ->
                      let uu____14623 =
                        let uu____14636 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____14636  in
                      (match uu____14623 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____14675 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____14682::uu____14683,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____14706 =
                 let uu____14719 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____14719  in
               (match uu____14706 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____14755  ->
                          let uu____14756 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14757 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14758 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14759 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14756 uu____14757 uu____14758 uu____14759);
                     (let uu____14760 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____14763 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____14760 [] uu____14763 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____14809 = lhs  in
           match uu____14809 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____14819 ->
                     let uu____14820 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____14820 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____14851 = p  in
           match uu____14851 with
           | (((u,k),xs,c),ps,(h,uu____14862,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14950 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____14950 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____14973 = h gs_xs  in
                      let uu____14974 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                         in
                      FStar_Syntax_Util.abs xs1 uu____14973 uu____14974  in
                    ((let uu____14980 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14980
                      then
                        let uu____14981 =
                          let uu____14984 =
                            let uu____14985 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____14985
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____14990 =
                            let uu____14993 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____14994 =
                              let uu____14997 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____14998 =
                                let uu____15001 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____15002 =
                                  let uu____15005 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____15006 =
                                    let uu____15009 =
                                      let uu____15010 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____15010
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____15015 =
                                      let uu____15018 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____15018]  in
                                    uu____15009 :: uu____15015  in
                                  uu____15005 :: uu____15006  in
                                uu____15001 :: uu____15002  in
                              uu____14997 :: uu____14998  in
                            uu____14993 :: uu____14994  in
                          uu____14984 :: uu____14990  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____14981
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___137_15048 =
           match uu___137_15048 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____15090 = p  in
           match uu____15090 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____15187 = FStar_List.nth ps i  in
               (match uu____15187 with
                | (pi,uu____15191) ->
                    let uu____15196 = FStar_List.nth xs i  in
                    (match uu____15196 with
                     | (xi,uu____15208) ->
                         let rec gs k =
                           let uu____15223 =
                             let uu____15236 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____15236  in
                           match uu____15223 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____15315)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____15328 = new_uvar r xs k_a  in
                                     (match uu____15328 with
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
                                          let uu____15350 = aux subst2 tl1
                                             in
                                          (match uu____15350 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____15377 =
                                                 let uu____15380 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____15380 :: gi_xs'  in
                                               let uu____15381 =
                                                 let uu____15384 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____15384 :: gi_ps'  in
                                               (uu____15377, uu____15381)))
                                  in
                               aux [] bs
                            in
                         let uu____15389 =
                           let uu____15390 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____15390
                            in
                         if uu____15389
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____15394 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____15394 with
                            | (g_xs,uu____15406) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____15417 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____15418 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_37  ->
                                         FStar_Pervasives_Native.Some _0_37)
                                     in
                                  FStar_Syntax_Util.abs xs uu____15417
                                    uu____15418
                                   in
                                let sub1 =
                                  let uu____15424 =
                                    let uu____15429 = p_scope orig  in
                                    let uu____15430 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____15433 =
                                      let uu____15436 =
                                        FStar_List.map
                                          (fun uu____15451  ->
                                             match uu____15451 with
                                             | (uu____15460,uu____15461,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____15436  in
                                    mk_problem uu____15429 orig uu____15430
                                      (p_rel orig) uu____15433
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_38  ->
                                       FStar_TypeChecker_Common.TProb _0_38)
                                    uu____15424
                                   in
                                ((let uu____15476 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15476
                                  then
                                    let uu____15477 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____15478 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____15477 uu____15478
                                  else ());
                                 (let wl2 =
                                    let uu____15481 =
                                      let uu____15484 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____15484
                                       in
                                    solve_prob orig uu____15481
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____15493 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_39  ->
                                       FStar_Pervasives_Native.Some _0_39)
                                    uu____15493)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____15534 = lhs  in
           match uu____15534 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____15572 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____15572 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____15605 =
                         let uu____15654 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____15654)  in
                       FStar_Pervasives_Native.Some uu____15605
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____15808 =
                            let uu____15815 =
                              let uu____15816 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____15816.FStar_Syntax_Syntax.n  in
                            (uu____15815, args)  in
                          match uu____15808 with
                          | (uu____15827,[]) ->
                              let uu____15830 =
                                let uu____15841 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____15841)  in
                              FStar_Pervasives_Native.Some uu____15830
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____15862,uu____15863) ->
                              let uu____15884 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15884 with
                               | (uv1,uv_args) ->
                                   let uu____15927 =
                                     let uu____15928 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15928.FStar_Syntax_Syntax.n  in
                                   (match uu____15927 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15938) ->
                                        let uu____15963 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15963 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15990  ->
                                                       let uu____15991 =
                                                         let uu____15992 =
                                                           let uu____15993 =
                                                             let uu____15998
                                                               =
                                                               let uu____15999
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15999
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15998
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15993
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15992
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15991))
                                                in
                                             let c1 =
                                               let uu____16009 =
                                                 let uu____16010 =
                                                   let uu____16015 =
                                                     let uu____16016 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16016
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____16015
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____16010
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____16009
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____16029 =
                                                 let uu____16032 =
                                                   let uu____16033 =
                                                     let uu____16036 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16036
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____16033
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____16032
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____16029
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____16055 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____16060,uu____16061) ->
                              let uu____16080 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____16080 with
                               | (uv1,uv_args) ->
                                   let uu____16123 =
                                     let uu____16124 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____16124.FStar_Syntax_Syntax.n  in
                                   (match uu____16123 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____16134) ->
                                        let uu____16159 =
                                          pat_vars env [] uv_args  in
                                        (match uu____16159 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____16186  ->
                                                       let uu____16187 =
                                                         let uu____16188 =
                                                           let uu____16189 =
                                                             let uu____16194
                                                               =
                                                               let uu____16195
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____16195
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____16194
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____16189
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____16188
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____16187))
                                                in
                                             let c1 =
                                               let uu____16205 =
                                                 let uu____16206 =
                                                   let uu____16211 =
                                                     let uu____16212 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16212
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____16211
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____16206
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____16205
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____16225 =
                                                 let uu____16228 =
                                                   let uu____16229 =
                                                     let uu____16232 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____16232
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____16229
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____16228
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____16225
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____16251 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____16258) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____16299 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____16299
                                  (fun _0_40  ->
                                     FStar_Pervasives_Native.Some _0_40)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____16335 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____16335 with
                                   | (args1,rest) ->
                                       let uu____16364 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____16364 with
                                        | (xs2,c2) ->
                                            let uu____16377 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____16377
                                              (fun uu____16401  ->
                                                 match uu____16401 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____16441 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____16441 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16509 =
                                         let uu____16514 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____16514
                                          in
                                       FStar_All.pipe_right uu____16509
                                         (fun _0_41  ->
                                            FStar_Pervasives_Native.Some
                                              _0_41))
                          | uu____16529 ->
                              let uu____16536 =
                                let uu____16541 =
                                  let uu____16542 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____16543 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____16544 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____16542 uu____16543 uu____16544
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____16541)
                                 in
                              FStar_Errors.raise_error uu____16536
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____16551 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____16551
                          (fun uu____16608  ->
                             match uu____16608 with
                             | (xs1,c1) ->
                                 let uu____16659 =
                                   let uu____16702 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____16702)
                                    in
                                 FStar_Pervasives_Native.Some uu____16659))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____16839 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____16859 = project orig env wl1 i st  in
                      match uu____16859 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____16873) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____16888 = imitate orig env wl1 st  in
                   match uu____16888 with
                   | Failed uu____16893 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____16932 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____16932 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____16955 = forced_lhs_pattern  in
                     (match uu____16955 with
                      | (lhs_t,uu____16957,uu____16958,uu____16959) ->
                          ((let uu____16961 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16961
                            then
                              let uu____16962 = lhs1  in
                              match uu____16962 with
                              | (t0,uu____16964,uu____16965,uu____16966) ->
                                  let uu____16967 = forced_lhs_pattern  in
                                  (match uu____16967 with
                                   | (t11,uu____16969,uu____16970,uu____16971)
                                       ->
                                       let uu____16972 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____16973 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____16972 uu____16973)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____16981 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____16981
                            then
                              ((let uu____16983 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16983
                                then
                                  let uu____16984 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____16985 = names_to_string rhs_vars
                                     in
                                  let uu____16986 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____16984 uu____16985 uu____16986
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____16990 =
                                  let uu____16991 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____16991 wl2  in
                                match uu____16990 with
                                | Failed uu____16992 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____17001 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____17001
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____17018 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____17018 with
                 | (hd1,uu____17034) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____17055 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____17068 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____17069 -> true
                      | uu____17086 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____17090 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____17090
                          then true
                          else
                            ((let uu____17093 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____17093
                              then
                                let uu____17094 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____17094
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
                    let uu____17114 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____17114 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____17127 =
                             let uu____17128 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____17128
                              in
                           giveup_or_defer1 orig uu____17127
                         else
                           (let uu____17130 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____17130
                            then
                              let uu____17131 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____17131
                               then
                                 let uu____17132 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____17132
                               else
                                 ((let uu____17137 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____17137
                                   then
                                     let uu____17138 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____17139 = names_to_string fvs1
                                        in
                                     let uu____17140 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____17138 uu____17139 uu____17140
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
                                (let uu____17144 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____17144
                                 then
                                   ((let uu____17146 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____17146
                                     then
                                       let uu____17147 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____17148 = names_to_string fvs1
                                          in
                                       let uu____17149 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____17147 uu____17148 uu____17149
                                     else ());
                                    (let uu____17151 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____17151))
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
                      (let uu____17162 =
                         let uu____17163 = FStar_Syntax_Free.names t1  in
                         check_head uu____17163 t2  in
                       if uu____17162
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____17174 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17174
                           then
                             let uu____17175 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____17176 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____17175 uu____17176
                           else ());
                          (let uu____17184 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____17184))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____17275 uu____17276 r =
                match (uu____17275, uu____17276) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____17474 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____17474
                    then
                      let uu____17475 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____17475
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____17499 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____17499
                        then
                          let uu____17500 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____17501 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____17502 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____17503 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____17504 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____17500 uu____17501 uu____17502 uu____17503
                            uu____17504
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____17570 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____17570 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____17584 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____17584 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____17638 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____17638
                                      in
                                   let uu____17641 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____17641 k3)
                            else
                              (let uu____17645 =
                                 let uu____17646 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____17647 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____17648 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____17646 uu____17647 uu____17648
                                  in
                               failwith uu____17645)
                           in
                        let uu____17649 =
                          let uu____17656 =
                            let uu____17669 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____17669  in
                          match uu____17656 with
                          | (bs,k1') ->
                              let uu____17694 =
                                let uu____17707 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____17707
                                 in
                              (match uu____17694 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____17735 =
                                       let uu____17740 = p_scope orig  in
                                       mk_problem uu____17740 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_42  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_42) uu____17735
                                      in
                                   let uu____17745 =
                                     let uu____17750 =
                                       let uu____17751 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____17751.FStar_Syntax_Syntax.n  in
                                     let uu____17754 =
                                       let uu____17755 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____17755.FStar_Syntax_Syntax.n  in
                                     (uu____17750, uu____17754)  in
                                   (match uu____17745 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____17764,uu____17765) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____17768,FStar_Syntax_Syntax.Tm_type
                                       uu____17769) -> (k2'_ys, [sub_prob])
                                    | uu____17772 ->
                                        let uu____17777 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____17777 with
                                         | (t,uu____17789) ->
                                             let uu____17790 =
                                               new_uvar r zs t  in
                                             (match uu____17790 with
                                              | (k_zs,uu____17802) ->
                                                  let kprob =
                                                    let uu____17804 =
                                                      let uu____17809 =
                                                        p_scope orig  in
                                                      mk_problem uu____17809
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_43  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_43) uu____17804
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____17649 with
                        | (k_u',sub_probs) ->
                            let uu____17822 =
                              let uu____17833 =
                                let uu____17834 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____17834
                                 in
                              let uu____17843 =
                                let uu____17846 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____17846  in
                              let uu____17849 =
                                let uu____17852 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____17852  in
                              (uu____17833, uu____17843, uu____17849)  in
                            (match uu____17822 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____17871 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____17871 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____17890 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____17890
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
                                            let uu____17894 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____17894 with
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
              let solve_one_pat uu____17951 uu____17952 =
                match (uu____17951, uu____17952) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____18070 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____18070
                      then
                        let uu____18071 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____18072 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____18071 uu____18072
                      else ());
                     (let uu____18074 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____18074
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____18093  ->
                               fun uu____18094  ->
                                 match (uu____18093, uu____18094) with
                                 | ((a,uu____18112),(t21,uu____18114)) ->
                                     let uu____18123 =
                                       let uu____18128 = p_scope orig  in
                                       let uu____18129 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____18128 orig
                                         uu____18129
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____18123
                                       (fun _0_44  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_44)) xs args2
                           in
                        let guard =
                          let uu____18135 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____18135  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____18150 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____18150 with
                         | (occurs_ok,uu____18158) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____18166 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____18166
                             then
                               let sol =
                                 let uu____18168 =
                                   let uu____18177 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____18177)  in
                                 TERM uu____18168  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____18184 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____18184
                                then
                                  let uu____18185 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____18185 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____18209,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____18235 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____18235
                                        then
                                          let uu____18236 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____18236
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____18243 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____18245 = lhs  in
              match uu____18245 with
              | (t1,u1,k1,args1) ->
                  let uu____18250 = rhs  in
                  (match uu____18250 with
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
                        | uu____18290 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____18300 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____18300 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____18318) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____18325 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____18325
                                     then
                                       let uu____18326 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____18326
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____18333 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18336 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18336
          then
            let uu____18337 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18337
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____18341 = FStar_Util.physical_equality t1 t2  in
             if uu____18341
             then
               let uu____18342 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____18342
             else
               ((let uu____18345 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____18345
                 then
                   let uu____18346 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____18347 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18348 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____18346
                     uu____18347 uu____18348
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____18351,uu____18352)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____18377,FStar_Syntax_Syntax.Tm_delayed uu____18378)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____18403,uu____18404)
                     ->
                     let uu____18431 =
                       let uu___175_18432 = problem  in
                       let uu____18433 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___175_18432.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18433;
                         FStar_TypeChecker_Common.relation =
                           (uu___175_18432.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___175_18432.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___175_18432.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___175_18432.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___175_18432.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___175_18432.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___175_18432.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___175_18432.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18431 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____18434,uu____18435) ->
                     let uu____18442 =
                       let uu___176_18443 = problem  in
                       let uu____18444 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_18443.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18444;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_18443.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_18443.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_18443.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_18443.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_18443.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_18443.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_18443.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_18443.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18442 wl
                 | (uu____18445,FStar_Syntax_Syntax.Tm_ascribed uu____18446)
                     ->
                     let uu____18473 =
                       let uu___177_18474 = problem  in
                       let uu____18475 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_18474.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_18474.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_18474.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18475;
                         FStar_TypeChecker_Common.element =
                           (uu___177_18474.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_18474.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_18474.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_18474.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_18474.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_18474.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18473 wl
                 | (uu____18476,FStar_Syntax_Syntax.Tm_meta uu____18477) ->
                     let uu____18484 =
                       let uu___178_18485 = problem  in
                       let uu____18486 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_18485.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_18485.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_18485.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18486;
                         FStar_TypeChecker_Common.element =
                           (uu___178_18485.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_18485.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_18485.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_18485.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_18485.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_18485.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18484 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____18488),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____18490)) ->
                     let uu____18499 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____18499
                 | (FStar_Syntax_Syntax.Tm_bvar uu____18500,uu____18501) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____18502,FStar_Syntax_Syntax.Tm_bvar uu____18503) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___138_18562 =
                       match uu___138_18562 with
                       | [] -> c
                       | bs ->
                           let uu____18584 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____18584
                        in
                     let uu____18593 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____18593 with
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
                                     let uu____18737 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____18737
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____18739 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_45  ->
                                        FStar_TypeChecker_Common.CProb _0_45)
                                     uu____18739))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___139_18821 =
                       match uu___139_18821 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18855 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____18855 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____18993 =
                                     let uu____18998 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____18999 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____18998
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____18999
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_46  ->
                                        FStar_TypeChecker_Common.TProb _0_46)
                                     uu____18993))
                 | (FStar_Syntax_Syntax.Tm_abs uu____19004,uu____19005) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____19032 -> true
                       | uu____19049 -> false  in
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
                         (let uu____19100 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___179_19108 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___179_19108.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___179_19108.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___179_19108.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___179_19108.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___179_19108.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___179_19108.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___179_19108.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___179_19108.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___179_19108.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___179_19108.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___179_19108.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___179_19108.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___179_19108.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___179_19108.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___179_19108.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___179_19108.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___179_19108.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___179_19108.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___179_19108.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___179_19108.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___179_19108.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___179_19108.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___179_19108.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___179_19108.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___179_19108.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___179_19108.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___179_19108.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___179_19108.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___179_19108.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___179_19108.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___179_19108.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___179_19108.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___179_19108.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___179_19108.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____19100 with
                          | (uu____19111,ty,uu____19113) ->
                              let uu____19114 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19114)
                        in
                     let uu____19115 =
                       let uu____19132 = maybe_eta t1  in
                       let uu____19139 = maybe_eta t2  in
                       (uu____19132, uu____19139)  in
                     (match uu____19115 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___180_19181 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_19181.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___180_19181.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___180_19181.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_19181.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_19181.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_19181.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_19181.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_19181.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19204 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19204
                          then
                            let uu____19205 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19205 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19220 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19220.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19220.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19220.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19220.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19220.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19220.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19220.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19220.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19244 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19244
                          then
                            let uu____19245 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19245 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19260 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19260.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19260.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19260.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19260.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19260.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19260.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19260.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19260.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19264 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____19281,FStar_Syntax_Syntax.Tm_abs uu____19282) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____19309 -> true
                       | uu____19326 -> false  in
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
                         (let uu____19377 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___179_19385 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___179_19385.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___179_19385.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___179_19385.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___179_19385.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___179_19385.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___179_19385.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___179_19385.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___179_19385.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___179_19385.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___179_19385.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___179_19385.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___179_19385.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___179_19385.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___179_19385.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___179_19385.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___179_19385.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___179_19385.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___179_19385.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___179_19385.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___179_19385.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___179_19385.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___179_19385.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___179_19385.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___179_19385.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___179_19385.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___179_19385.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___179_19385.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___179_19385.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___179_19385.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___179_19385.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___179_19385.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___179_19385.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___179_19385.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___179_19385.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____19377 with
                          | (uu____19388,ty,uu____19390) ->
                              let uu____19391 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19391)
                        in
                     let uu____19392 =
                       let uu____19409 = maybe_eta t1  in
                       let uu____19416 = maybe_eta t2  in
                       (uu____19409, uu____19416)  in
                     (match uu____19392 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___180_19458 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_19458.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___180_19458.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___180_19458.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_19458.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_19458.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_19458.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_19458.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_19458.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19481 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19481
                          then
                            let uu____19482 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19482 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19497 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19497.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19497.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19497.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19497.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19497.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19497.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19497.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19497.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19521 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19521
                          then
                            let uu____19522 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19522 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___181_19537 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___181_19537.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___181_19537.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___181_19537.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___181_19537.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___181_19537.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___181_19537.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___181_19537.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___181_19537.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19541 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____19573 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____19573) &&
                          (let uu____19585 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____19585))
                         &&
                         (let uu____19600 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____19600 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___140_19612 =
                                match uu___140_19612 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____19613 -> true
                                | uu____19614 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____19615 -> false)
                        in
                     let uu____19616 = as_refinement should_delta env wl t1
                        in
                     (match uu____19616 with
                      | (x11,phi1) ->
                          let uu____19623 =
                            as_refinement should_delta env wl t2  in
                          (match uu____19623 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____19631 =
                                   let uu____19636 = p_scope orig  in
                                   mk_problem uu____19636 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_47  ->
                                      FStar_TypeChecker_Common.TProb _0_47)
                                   uu____19631
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
                                 let uu____19676 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____19676
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____19682 =
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
                                   let uu____19688 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19688 impl
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
                                   let uu____19697 =
                                     let uu____19702 =
                                       let uu____19703 = p_scope orig  in
                                       let uu____19710 =
                                         let uu____19717 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____19717]  in
                                       FStar_List.append uu____19703
                                         uu____19710
                                        in
                                     mk_problem uu____19702 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_48  ->
                                        FStar_TypeChecker_Common.TProb _0_48)
                                     uu____19697
                                    in
                                 let uu____19726 =
                                   solve env1
                                     (let uu___182_19728 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___182_19728.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___182_19728.smt_ok);
                                        tcenv = (uu___182_19728.tcenv)
                                      })
                                    in
                                 (match uu____19726 with
                                  | Failed uu____19735 -> fallback ()
                                  | Success uu____19740 ->
                                      let guard =
                                        let uu____19744 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____19749 =
                                          let uu____19750 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____19750
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____19744
                                          uu____19749
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___183_19759 = wl1  in
                                        {
                                          attempting =
                                            (uu___183_19759.attempting);
                                          wl_deferred =
                                            (uu___183_19759.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___183_19759.defer_ok);
                                          smt_ok = (uu___183_19759.smt_ok);
                                          tcenv = (uu___183_19759.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19761,FStar_Syntax_Syntax.Tm_uvar uu____19762) ->
                     let uu____19795 = destruct_flex_t t1  in
                     let uu____19796 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19795 uu____19796
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19797;
                       FStar_Syntax_Syntax.pos = uu____19798;
                       FStar_Syntax_Syntax.vars = uu____19799;_},uu____19800),FStar_Syntax_Syntax.Tm_uvar
                    uu____19801) ->
                     let uu____19854 = destruct_flex_t t1  in
                     let uu____19855 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19854 uu____19855
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19856,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19857;
                       FStar_Syntax_Syntax.pos = uu____19858;
                       FStar_Syntax_Syntax.vars = uu____19859;_},uu____19860))
                     ->
                     let uu____19913 = destruct_flex_t t1  in
                     let uu____19914 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19913 uu____19914
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19915;
                       FStar_Syntax_Syntax.pos = uu____19916;
                       FStar_Syntax_Syntax.vars = uu____19917;_},uu____19918),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19919;
                       FStar_Syntax_Syntax.pos = uu____19920;
                       FStar_Syntax_Syntax.vars = uu____19921;_},uu____19922))
                     ->
                     let uu____19995 = destruct_flex_t t1  in
                     let uu____19996 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19995 uu____19996
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19997,uu____19998) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____20015 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____20015 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20022;
                       FStar_Syntax_Syntax.pos = uu____20023;
                       FStar_Syntax_Syntax.vars = uu____20024;_},uu____20025),uu____20026)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____20063 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____20063 t2 wl
                 | (uu____20070,FStar_Syntax_Syntax.Tm_uvar uu____20071) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____20088,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20089;
                       FStar_Syntax_Syntax.pos = uu____20090;
                       FStar_Syntax_Syntax.vars = uu____20091;_},uu____20092))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____20129,FStar_Syntax_Syntax.Tm_type uu____20130) ->
                     solve_t' env
                       (let uu___184_20148 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20148.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20148.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20148.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20148.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20148.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20148.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20148.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20148.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20148.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20149;
                       FStar_Syntax_Syntax.pos = uu____20150;
                       FStar_Syntax_Syntax.vars = uu____20151;_},uu____20152),FStar_Syntax_Syntax.Tm_type
                    uu____20153) ->
                     solve_t' env
                       (let uu___184_20191 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20191.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20191.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20191.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20191.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20191.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20191.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20191.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20191.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20191.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____20192,FStar_Syntax_Syntax.Tm_arrow uu____20193) ->
                     solve_t' env
                       (let uu___184_20223 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20223.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20223.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20223.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20223.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20223.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20223.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20223.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20223.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20223.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20224;
                       FStar_Syntax_Syntax.pos = uu____20225;
                       FStar_Syntax_Syntax.vars = uu____20226;_},uu____20227),FStar_Syntax_Syntax.Tm_arrow
                    uu____20228) ->
                     solve_t' env
                       (let uu___184_20278 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_20278.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___184_20278.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___184_20278.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___184_20278.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_20278.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___184_20278.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_20278.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_20278.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_20278.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____20279,uu____20280) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20299 =
                          let uu____20300 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20300
                           in
                        if uu____20299
                        then
                          let uu____20301 =
                            FStar_All.pipe_left
                              (fun _0_49  ->
                                 FStar_TypeChecker_Common.TProb _0_49)
                              (let uu___185_20307 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___185_20307.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___185_20307.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___185_20307.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___185_20307.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___185_20307.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___185_20307.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___185_20307.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___185_20307.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___185_20307.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20308 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20301 uu____20308 t2
                            wl
                        else
                          (let uu____20316 = base_and_refinement env t2  in
                           match uu____20316 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20345 =
                                      FStar_All.pipe_left
                                        (fun _0_50  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_50)
                                        (let uu___186_20351 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___186_20351.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___186_20351.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___186_20351.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___186_20351.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___186_20351.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___186_20351.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___186_20351.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___186_20351.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___186_20351.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20352 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20345
                                      uu____20352 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___187_20366 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___187_20366.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___187_20366.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20369 =
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
                                             _0_51) uu____20369
                                       in
                                    let guard =
                                      let uu____20381 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20381
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
                         uu____20389;
                       FStar_Syntax_Syntax.pos = uu____20390;
                       FStar_Syntax_Syntax.vars = uu____20391;_},uu____20392),uu____20393)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20432 =
                          let uu____20433 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20433
                           in
                        if uu____20432
                        then
                          let uu____20434 =
                            FStar_All.pipe_left
                              (fun _0_52  ->
                                 FStar_TypeChecker_Common.TProb _0_52)
                              (let uu___185_20440 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___185_20440.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___185_20440.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___185_20440.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___185_20440.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___185_20440.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___185_20440.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___185_20440.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___185_20440.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___185_20440.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20441 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20434 uu____20441 t2
                            wl
                        else
                          (let uu____20449 = base_and_refinement env t2  in
                           match uu____20449 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20478 =
                                      FStar_All.pipe_left
                                        (fun _0_53  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_53)
                                        (let uu___186_20484 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___186_20484.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___186_20484.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___186_20484.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___186_20484.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___186_20484.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___186_20484.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___186_20484.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___186_20484.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___186_20484.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20485 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20478
                                      uu____20485 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___187_20499 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___187_20499.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___187_20499.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20502 =
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
                                             _0_54) uu____20502
                                       in
                                    let guard =
                                      let uu____20514 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20514
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____20522,FStar_Syntax_Syntax.Tm_uvar uu____20523) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20541 = base_and_refinement env t1  in
                        match uu____20541 with
                        | (t_base,uu____20553) ->
                            solve_t env
                              (let uu___188_20567 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_20567.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___188_20567.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_20567.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_20567.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___188_20567.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_20567.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_20567.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_20567.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____20568,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20569;
                       FStar_Syntax_Syntax.pos = uu____20570;
                       FStar_Syntax_Syntax.vars = uu____20571;_},uu____20572))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20610 = base_and_refinement env t1  in
                        match uu____20610 with
                        | (t_base,uu____20622) ->
                            solve_t env
                              (let uu___188_20636 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_20636.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___188_20636.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_20636.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_20636.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___188_20636.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_20636.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_20636.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_20636.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____20637,uu____20638) ->
                     let t21 =
                       let uu____20648 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____20648  in
                     solve_t env
                       (let uu___189_20672 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___189_20672.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___189_20672.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___189_20672.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___189_20672.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___189_20672.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___189_20672.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___189_20672.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___189_20672.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___189_20672.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____20673,FStar_Syntax_Syntax.Tm_refine uu____20674) ->
                     let t11 =
                       let uu____20684 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____20684  in
                     solve_t env
                       (let uu___190_20708 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___190_20708.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___190_20708.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___190_20708.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___190_20708.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___190_20708.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___190_20708.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___190_20708.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___190_20708.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___190_20708.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                     let sc_prob =
                       let uu____20788 =
                         let uu____20793 = p_scope orig  in
                         mk_problem uu____20793 orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                         uu____20788
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____20983 = br1  in
                           (match uu____20983 with
                            | (p1,w1,uu____21002) ->
                                let uu____21015 = br2  in
                                (match uu____21015 with
                                 | (p2,w2,uu____21030) ->
                                     let uu____21035 =
                                       let uu____21036 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____21036  in
                                     if uu____21035
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____21044 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____21044 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____21087 = br2  in
                                            (match uu____21087 with
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
                                                   let uu____21118 =
                                                     p_scope orig  in
                                                   let uu____21125 =
                                                     let uu____21132 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____21132
                                                      in
                                                   FStar_List.append
                                                     uu____21118 uu____21125
                                                    in
                                                 let uu____21143 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____21158,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____21171) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____21204 =
                                                         let uu____21207 =
                                                           let uu____21208 =
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
                                                             uu____21208
                                                            in
                                                         [uu____21207]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21204
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____21143
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____21232 =
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
                                                          uu____21232
                                                         in
                                                      let uu____21243 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____21243
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____21304 -> FStar_Pervasives_Native.None  in
                     let by_smt uu____21340 =
                       let guard = guard_of_prob env problem t1 t2  in
                       let uu____21344 = solve_prob orig guard [] wl  in
                       solve env uu____21344  in
                     let uu____21345 = solve_branches brs1 brs2  in
                     (match uu____21345 with
                      | FStar_Pervasives_Native.None  ->
                          if wl.smt_ok
                          then by_smt ()
                          else
                            giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let formula =
                            let uu____21362 =
                              FStar_List.map
                                (fun p  ->
                                   FStar_Pervasives_Native.fst (p_guard p))
                                sub_probs1
                               in
                            FStar_Syntax_Util.mk_conj_l uu____21362  in
                          let tx = FStar_Syntax_Unionfind.new_transaction ()
                             in
                          let wl1 =
                            solve_prob orig
                              (FStar_Pervasives_Native.Some formula) [] wl
                             in
                          let uu____21369 =
                            solve env
                              (attempt sub_probs1
                                 (let uu___191_21371 = wl1  in
                                  {
                                    attempting = (uu___191_21371.attempting);
                                    wl_deferred =
                                      (uu___191_21371.wl_deferred);
                                    ctr = (uu___191_21371.ctr);
                                    defer_ok = (uu___191_21371.defer_ok);
                                    smt_ok = false;
                                    tcenv = (uu___191_21371.tcenv)
                                  }))
                             in
                          (match uu____21369 with
                           | Success ds ->
                               (FStar_Syntax_Unionfind.commit tx; Success ds)
                           | Failed uu____21374 ->
                               (FStar_Syntax_Unionfind.rollback tx; by_smt ())))
                 | (FStar_Syntax_Syntax.Tm_match uu____21380,uu____21381) ->
                     let head1 =
                       let uu____21407 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21407
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21451 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21451
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21493 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21493
                       then
                         let uu____21494 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21495 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21496 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21494 uu____21495 uu____21496
                       else ());
                      (let uu____21498 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21498
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21513 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21513
                          then
                            let guard =
                              let uu____21525 =
                                let uu____21526 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21526 = FStar_Syntax_Util.Equal  in
                              if uu____21525
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21530 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_Pervasives_Native.Some _0_58)
                                   uu____21530)
                               in
                            let uu____21533 = solve_prob orig guard [] wl  in
                            solve env uu____21533
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____21536,uu____21537) ->
                     let head1 =
                       let uu____21547 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21547
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21591 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21591
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21633 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21633
                       then
                         let uu____21634 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21635 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21636 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21634 uu____21635 uu____21636
                       else ());
                      (let uu____21638 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21638
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21653 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21653
                          then
                            let guard =
                              let uu____21665 =
                                let uu____21666 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21666 = FStar_Syntax_Util.Equal  in
                              if uu____21665
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21670 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_Pervasives_Native.Some _0_59)
                                   uu____21670)
                               in
                            let uu____21673 = solve_prob orig guard [] wl  in
                            solve env uu____21673
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____21676,uu____21677) ->
                     let head1 =
                       let uu____21681 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21681
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21725 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21725
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21767 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21767
                       then
                         let uu____21768 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21769 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21770 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21768 uu____21769 uu____21770
                       else ());
                      (let uu____21772 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21772
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21787 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21787
                          then
                            let guard =
                              let uu____21799 =
                                let uu____21800 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21800 = FStar_Syntax_Util.Equal  in
                              if uu____21799
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21804 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____21804)
                               in
                            let uu____21807 = solve_prob orig guard [] wl  in
                            solve env uu____21807
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____21810,uu____21811)
                     ->
                     let head1 =
                       let uu____21815 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21815
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21859 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21859
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21901 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21901
                       then
                         let uu____21902 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21903 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21904 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21902 uu____21903 uu____21904
                       else ());
                      (let uu____21906 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21906
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21921 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21921
                          then
                            let guard =
                              let uu____21933 =
                                let uu____21934 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21934 = FStar_Syntax_Util.Equal  in
                              if uu____21933
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21938 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____21938)
                               in
                            let uu____21941 = solve_prob orig guard [] wl  in
                            solve env uu____21941
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____21944,uu____21945) ->
                     let head1 =
                       let uu____21949 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21949
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21993 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21993
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22035 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22035
                       then
                         let uu____22036 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22037 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22038 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22036 uu____22037 uu____22038
                       else ());
                      (let uu____22040 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22040
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22055 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22055
                          then
                            let guard =
                              let uu____22067 =
                                let uu____22068 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22068 = FStar_Syntax_Util.Equal  in
                              if uu____22067
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22072 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____22072)
                               in
                            let uu____22075 = solve_prob orig guard [] wl  in
                            solve env uu____22075
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____22078,uu____22079) ->
                     let head1 =
                       let uu____22097 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22097
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22141 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22141
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22183 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22183
                       then
                         let uu____22184 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22185 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22186 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22184 uu____22185 uu____22186
                       else ());
                      (let uu____22188 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22188
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22203 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22203
                          then
                            let guard =
                              let uu____22215 =
                                let uu____22216 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22216 = FStar_Syntax_Util.Equal  in
                              if uu____22215
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22220 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   uu____22220)
                               in
                            let uu____22223 = solve_prob orig guard [] wl  in
                            solve env uu____22223
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22226,FStar_Syntax_Syntax.Tm_match uu____22227) ->
                     let head1 =
                       let uu____22253 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22253
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22297 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22297
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22339 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22339
                       then
                         let uu____22340 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22341 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22342 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22340 uu____22341 uu____22342
                       else ());
                      (let uu____22344 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22344
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22359 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22359
                          then
                            let guard =
                              let uu____22371 =
                                let uu____22372 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22372 = FStar_Syntax_Util.Equal  in
                              if uu____22371
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22376 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   uu____22376)
                               in
                            let uu____22379 = solve_prob orig guard [] wl  in
                            solve env uu____22379
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22382,FStar_Syntax_Syntax.Tm_uinst uu____22383) ->
                     let head1 =
                       let uu____22393 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22393
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22437 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22437
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22479 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22479
                       then
                         let uu____22480 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22481 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22482 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22480 uu____22481 uu____22482
                       else ());
                      (let uu____22484 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22484
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22499 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22499
                          then
                            let guard =
                              let uu____22511 =
                                let uu____22512 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22512 = FStar_Syntax_Util.Equal  in
                              if uu____22511
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22516 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   uu____22516)
                               in
                            let uu____22519 = solve_prob orig guard [] wl  in
                            solve env uu____22519
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22522,FStar_Syntax_Syntax.Tm_name uu____22523) ->
                     let head1 =
                       let uu____22527 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22527
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22571 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22571
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22613 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22613
                       then
                         let uu____22614 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22615 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22616 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22614 uu____22615 uu____22616
                       else ());
                      (let uu____22618 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22618
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22633 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22633
                          then
                            let guard =
                              let uu____22645 =
                                let uu____22646 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22646 = FStar_Syntax_Util.Equal  in
                              if uu____22645
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22650 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   uu____22650)
                               in
                            let uu____22653 = solve_prob orig guard [] wl  in
                            solve env uu____22653
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22656,FStar_Syntax_Syntax.Tm_constant uu____22657)
                     ->
                     let head1 =
                       let uu____22661 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22661
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22705 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22705
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22747 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22747
                       then
                         let uu____22748 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22749 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22750 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22748 uu____22749 uu____22750
                       else ());
                      (let uu____22752 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22752
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22767 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22767
                          then
                            let guard =
                              let uu____22779 =
                                let uu____22780 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22780 = FStar_Syntax_Util.Equal  in
                              if uu____22779
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22784 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   uu____22784)
                               in
                            let uu____22787 = solve_prob orig guard [] wl  in
                            solve env uu____22787
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22790,FStar_Syntax_Syntax.Tm_fvar uu____22791) ->
                     let head1 =
                       let uu____22795 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22795
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22839 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22839
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22881 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22881
                       then
                         let uu____22882 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22883 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22884 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22882 uu____22883 uu____22884
                       else ());
                      (let uu____22886 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22886
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22901 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22901
                          then
                            let guard =
                              let uu____22913 =
                                let uu____22914 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22914 = FStar_Syntax_Util.Equal  in
                              if uu____22913
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22918 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_Pervasives_Native.Some _0_68)
                                   uu____22918)
                               in
                            let uu____22921 = solve_prob orig guard [] wl  in
                            solve env uu____22921
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22924,FStar_Syntax_Syntax.Tm_app uu____22925) ->
                     let head1 =
                       let uu____22943 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22943
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22987 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22987
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____23029 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____23029
                       then
                         let uu____23030 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____23031 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____23032 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____23030 uu____23031 uu____23032
                       else ());
                      (let uu____23034 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____23034
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____23049 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____23049
                          then
                            let guard =
                              let uu____23061 =
                                let uu____23062 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____23062 = FStar_Syntax_Util.Equal  in
                              if uu____23061
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____23066 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_Pervasives_Native.Some _0_69)
                                   uu____23066)
                               in
                            let uu____23069 = solve_prob orig guard [] wl  in
                            solve env uu____23069
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____23072,FStar_Syntax_Syntax.Tm_let uu____23073) ->
                     let uu____23098 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____23098
                     then
                       let uu____23099 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____23099
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____23101,uu____23102) ->
                     let uu____23115 =
                       let uu____23120 =
                         let uu____23121 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____23122 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____23123 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____23124 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____23121 uu____23122 uu____23123 uu____23124
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____23120)
                        in
                     FStar_Errors.raise_error uu____23115
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____23125,FStar_Syntax_Syntax.Tm_let uu____23126) ->
                     let uu____23139 =
                       let uu____23144 =
                         let uu____23145 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____23146 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____23147 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____23148 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____23145 uu____23146 uu____23147 uu____23148
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____23144)
                        in
                     FStar_Errors.raise_error uu____23139
                       t1.FStar_Syntax_Syntax.pos
                 | uu____23149 -> giveup env "head tag mismatch" orig)))))

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
          let uu____23185 = p_scope orig  in
          mk_problem uu____23185 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____23198 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23198
           then
             let uu____23199 =
               let uu____23200 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23200  in
             let uu____23201 =
               let uu____23202 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23202  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23199 uu____23201
           else ());
          (let uu____23204 =
             let uu____23205 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23205  in
           if uu____23204
           then
             let uu____23206 =
               let uu____23207 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23208 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23207 uu____23208
                in
             giveup env uu____23206 orig
           else
             (let ret_sub_prob =
                let uu____23211 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_70  -> FStar_TypeChecker_Common.TProb _0_70)
                  uu____23211
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____23238  ->
                     fun uu____23239  ->
                       match (uu____23238, uu____23239) with
                       | ((a1,uu____23257),(a2,uu____23259)) ->
                           let uu____23268 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_71  ->
                                FStar_TypeChecker_Common.TProb _0_71)
                             uu____23268)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____23281 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____23281  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23313 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23320)::[] -> wp1
              | uu____23337 ->
                  let uu____23346 =
                    let uu____23347 =
                      let uu____23348 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23348  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23347
                     in
                  failwith uu____23346
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23356 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23356]
              | x -> x  in
            let uu____23358 =
              let uu____23367 =
                let uu____23368 =
                  let uu____23369 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23369 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23368  in
              [uu____23367]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23358;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23370 = lift_c1 ()  in solve_eq uu____23370 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___141_23376  ->
                       match uu___141_23376 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23377 -> false))
                in
             let uu____23378 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23412)::uu____23413,(wp2,uu____23415)::uu____23416)
                   -> (wp1, wp2)
               | uu____23473 ->
                   let uu____23494 =
                     let uu____23499 =
                       let uu____23500 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23501 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23500 uu____23501
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23499)
                      in
                   FStar_Errors.raise_error uu____23494
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23378 with
             | (wpc1,wpc2) ->
                 let uu____23520 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23520
                 then
                   let uu____23523 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23523 wl
                 else
                   (let uu____23527 =
                      let uu____23534 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23534  in
                    match uu____23527 with
                    | (c2_decl,qualifiers) ->
                        let uu____23555 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23555
                        then
                          let c1_repr =
                            let uu____23559 =
                              let uu____23560 =
                                let uu____23561 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23561  in
                              let uu____23562 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23560 uu____23562
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23559
                             in
                          let c2_repr =
                            let uu____23564 =
                              let uu____23565 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23566 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23565 uu____23566
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23564
                             in
                          let prob =
                            let uu____23568 =
                              let uu____23573 =
                                let uu____23574 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____23575 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23574
                                  uu____23575
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23573
                               in
                            FStar_TypeChecker_Common.TProb uu____23568  in
                          let wl1 =
                            let uu____23577 =
                              let uu____23580 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____23580  in
                            solve_prob orig uu____23577 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23589 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23589
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23592 =
                                     let uu____23599 =
                                       let uu____23600 =
                                         let uu____23615 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23616 =
                                           let uu____23619 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23620 =
                                             let uu____23623 =
                                               let uu____23624 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23624
                                                in
                                             [uu____23623]  in
                                           uu____23619 :: uu____23620  in
                                         (uu____23615, uu____23616)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23600
                                        in
                                     FStar_Syntax_Syntax.mk uu____23599  in
                                   uu____23592 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23633 =
                                    let uu____23640 =
                                      let uu____23641 =
                                        let uu____23656 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23657 =
                                          let uu____23660 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____23661 =
                                            let uu____23664 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____23665 =
                                              let uu____23668 =
                                                let uu____23669 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23669
                                                 in
                                              [uu____23668]  in
                                            uu____23664 :: uu____23665  in
                                          uu____23660 :: uu____23661  in
                                        (uu____23656, uu____23657)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23641
                                       in
                                    FStar_Syntax_Syntax.mk uu____23640  in
                                  uu____23633 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23676 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_TypeChecker_Common.TProb _0_72)
                               uu____23676
                              in
                           let wl1 =
                             let uu____23686 =
                               let uu____23689 =
                                 let uu____23692 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23692 g  in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_Pervasives_Native.Some _0_73)
                                 uu____23689
                                in
                             solve_prob orig uu____23686 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23705 = FStar_Util.physical_equality c1 c2  in
        if uu____23705
        then
          let uu____23706 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23706
        else
          ((let uu____23709 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23709
            then
              let uu____23710 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____23711 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23710
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23711
            else ());
           (let uu____23713 =
              let uu____23718 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____23719 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____23718, uu____23719)  in
            match uu____23713 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23723),FStar_Syntax_Syntax.Total
                    (t2,uu____23725)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23742 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23742 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23745,FStar_Syntax_Syntax.Total uu____23746) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23764),FStar_Syntax_Syntax.Total
                    (t2,uu____23766)) ->
                     let uu____23783 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23783 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23787),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23789)) ->
                     let uu____23806 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23806 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23810),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23812)) ->
                     let uu____23829 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23829 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23832,FStar_Syntax_Syntax.Comp uu____23833) ->
                     let uu____23842 =
                       let uu___192_23847 = problem  in
                       let uu____23852 =
                         let uu____23853 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23853
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___192_23847.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23852;
                         FStar_TypeChecker_Common.relation =
                           (uu___192_23847.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___192_23847.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___192_23847.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___192_23847.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___192_23847.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___192_23847.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___192_23847.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___192_23847.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23842 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23854,FStar_Syntax_Syntax.Comp uu____23855) ->
                     let uu____23864 =
                       let uu___192_23869 = problem  in
                       let uu____23874 =
                         let uu____23875 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23875
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___192_23869.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23874;
                         FStar_TypeChecker_Common.relation =
                           (uu___192_23869.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___192_23869.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___192_23869.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___192_23869.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___192_23869.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___192_23869.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___192_23869.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___192_23869.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23864 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23876,FStar_Syntax_Syntax.GTotal uu____23877) ->
                     let uu____23886 =
                       let uu___193_23891 = problem  in
                       let uu____23896 =
                         let uu____23897 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23897
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___193_23891.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___193_23891.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___193_23891.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23896;
                         FStar_TypeChecker_Common.element =
                           (uu___193_23891.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___193_23891.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___193_23891.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___193_23891.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___193_23891.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___193_23891.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23886 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23898,FStar_Syntax_Syntax.Total uu____23899) ->
                     let uu____23908 =
                       let uu___193_23913 = problem  in
                       let uu____23918 =
                         let uu____23919 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23919
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___193_23913.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___193_23913.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___193_23913.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23918;
                         FStar_TypeChecker_Common.element =
                           (uu___193_23913.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___193_23913.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___193_23913.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___193_23913.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___193_23913.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___193_23913.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23908 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23920,FStar_Syntax_Syntax.Comp uu____23921) ->
                     let uu____23922 =
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
                     if uu____23922
                     then
                       let uu____23923 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____23923 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____23929 =
                            let uu____23934 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____23934
                            then (c1_comp, c2_comp)
                            else
                              (let uu____23940 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____23941 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____23940, uu____23941))
                             in
                          match uu____23929 with
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
                           (let uu____23948 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23948
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23950 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____23950 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23953 =
                                  let uu____23954 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____23955 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____23954 uu____23955
                                   in
                                giveup env uu____23953 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23962 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____24000  ->
              match uu____24000 with
              | (uu____24013,uu____24014,u,uu____24016,uu____24017,uu____24018)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23962 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24051 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24051 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24069 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24097  ->
                match uu____24097 with
                | (u1,u2) ->
                    let uu____24104 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24105 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24104 uu____24105))
         in
      FStar_All.pipe_right uu____24069 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24126,[])) -> "{}"
      | uu____24151 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24168 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____24168
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24171 =
              FStar_List.map
                (fun uu____24181  ->
                   match uu____24181 with
                   | (uu____24186,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24171 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24191 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24191 imps
  
let new_t_problem :
  'Auu____24206 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____24206 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____24206)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____24246 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____24246
                then
                  let uu____24247 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____24248 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24247
                    (rel_to_string rel) uu____24248
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
            let uu____24280 =
              let uu____24283 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_74  -> FStar_Pervasives_Native.Some _0_74)
                uu____24283
               in
            FStar_Syntax_Syntax.new_bv uu____24280 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____24292 =
              let uu____24295 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_75  -> FStar_Pervasives_Native.Some _0_75)
                uu____24295
               in
            let uu____24298 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____24292 uu____24298  in
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
          let uu____24334 = FStar_Options.eager_inference ()  in
          if uu____24334
          then
            let uu___194_24335 = probs  in
            {
              attempting = (uu___194_24335.attempting);
              wl_deferred = (uu___194_24335.wl_deferred);
              ctr = (uu___194_24335.ctr);
              defer_ok = false;
              smt_ok = (uu___194_24335.smt_ok);
              tcenv = (uu___194_24335.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____24346 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____24346
              then
                let uu____24347 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24347
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
          ((let uu____24365 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____24365
            then
              let uu____24366 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24366
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____24370 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____24370
             then
               let uu____24371 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24371
             else ());
            (let f2 =
               let uu____24374 =
                 let uu____24375 = FStar_Syntax_Util.unmeta f1  in
                 uu____24375.FStar_Syntax_Syntax.n  in
               match uu____24374 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24379 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___195_24380 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___195_24380.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___195_24380.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___195_24380.FStar_TypeChecker_Env.implicits)
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
            let uu____24405 =
              let uu____24406 =
                let uu____24407 =
                  let uu____24408 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____24408
                    (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24407;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____24406  in
            FStar_All.pipe_left
              (fun _0_77  -> FStar_Pervasives_Native.Some _0_77) uu____24405
  
let with_guard_no_simp :
  'Auu____24439 .
    'Auu____24439 ->
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
            let uu____24462 =
              let uu____24463 =
                let uu____24464 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____24464
                  (fun _0_78  -> FStar_TypeChecker_Common.NonTrivial _0_78)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24463;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24462
  
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
          (let uu____24510 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24510
           then
             let uu____24511 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24512 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24511
               uu____24512
           else ());
          (let prob =
             let uu____24515 =
               let uu____24520 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24520
                in
             FStar_All.pipe_left
               (fun _0_79  -> FStar_TypeChecker_Common.TProb _0_79)
               uu____24515
              in
           let g =
             let uu____24528 =
               let uu____24531 = singleton' env prob smt_ok  in
               solve_and_commit env uu____24531
                 (fun uu____24533  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____24528  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24557 = try_teq true env t1 t2  in
        match uu____24557 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____24561 = FStar_TypeChecker_Env.get_range env  in
              let uu____24562 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____24561 uu____24562);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24569 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____24569
              then
                let uu____24570 = FStar_Syntax_Print.term_to_string t1  in
                let uu____24571 = FStar_Syntax_Print.term_to_string t2  in
                let uu____24572 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24570
                  uu____24571 uu____24572
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
          let uu____24594 = FStar_TypeChecker_Env.get_range env  in
          let uu____24595 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____24594 uu____24595
  
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
        (let uu____24620 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24620
         then
           let uu____24621 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____24622 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____24621 uu____24622
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____24626 =
             let uu____24631 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24631 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_80  -> FStar_TypeChecker_Common.CProb _0_80) uu____24626
            in
         let uu____24636 =
           let uu____24639 = singleton env prob  in
           solve_and_commit env uu____24639
             (fun uu____24641  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____24636)
  
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
      fun uu____24676  ->
        match uu____24676 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24719 =
                 let uu____24724 =
                   let uu____24725 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____24726 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____24725 uu____24726
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____24724)  in
               let uu____24727 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____24719 uu____24727)
               in
            let equiv1 v1 v' =
              let uu____24739 =
                let uu____24744 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24745 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24744, uu____24745)  in
              match uu____24739 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24764 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24794 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24794 with
                      | FStar_Syntax_Syntax.U_unif uu____24801 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24830  ->
                                    match uu____24830 with
                                    | (u,v') ->
                                        let uu____24839 = equiv1 v1 v'  in
                                        if uu____24839
                                        then
                                          let uu____24842 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24842 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24858 -> []))
               in
            let uu____24863 =
              let wl =
                let uu___196_24867 = empty_worklist env  in
                {
                  attempting = (uu___196_24867.attempting);
                  wl_deferred = (uu___196_24867.wl_deferred);
                  ctr = (uu___196_24867.ctr);
                  defer_ok = false;
                  smt_ok = (uu___196_24867.smt_ok);
                  tcenv = (uu___196_24867.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24885  ->
                      match uu____24885 with
                      | (lb,v1) ->
                          let uu____24892 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24892 with
                           | USolved wl1 -> ()
                           | uu____24894 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24904 =
              match uu____24904 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24913) -> true
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
                      uu____24936,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24938,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24949) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24956,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24964 -> false)
               in
            let uu____24969 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24984  ->
                      match uu____24984 with
                      | (u,v1) ->
                          let uu____24991 = check_ineq (u, v1)  in
                          if uu____24991
                          then true
                          else
                            ((let uu____24994 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24994
                              then
                                let uu____24995 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24996 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24995
                                  uu____24996
                              else ());
                             false)))
               in
            if uu____24969
            then ()
            else
              ((let uu____25000 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25000
                then
                  ((let uu____25002 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25002);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25012 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25012))
                else ());
               (let uu____25022 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25022))
  
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
      let fail1 uu____25080 =
        match uu____25080 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____25094 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25094
       then
         let uu____25095 = wl_to_string wl  in
         let uu____25096 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____25095 uu____25096
       else ());
      (let g1 =
         let uu____25111 = solve_and_commit env wl fail1  in
         match uu____25111 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___197_25124 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___197_25124.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___197_25124.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___197_25124.FStar_TypeChecker_Env.implicits)
             }
         | uu____25129 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___198_25133 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___198_25133.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___198_25133.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___198_25133.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____25161 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25161 with
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
            let uu___199_25284 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___199_25284.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___199_25284.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___199_25284.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25285 =
            let uu____25286 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25286  in
          if uu____25285
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____25294 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____25295 =
                       let uu____25296 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____25296
                        in
                     FStar_Errors.diag uu____25294 uu____25295)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____25300 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____25301 =
                        let uu____25302 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____25302
                         in
                      FStar_Errors.diag uu____25300 uu____25301)
                   else ();
                   (let uu____25305 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____25305 "discharge_guard'"
                      env vc1);
                   (let uu____25306 = check_trivial vc1  in
                    match uu____25306 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____25313 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25314 =
                                let uu____25315 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____25315
                                 in
                              FStar_Errors.diag uu____25313 uu____25314)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____25320 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25321 =
                                let uu____25322 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____25322
                                 in
                              FStar_Errors.diag uu____25320 uu____25321)
                           else ();
                           (let vcs =
                              let uu____25333 = FStar_Options.use_tactics ()
                                 in
                              if uu____25333
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____25353  ->
                                     (let uu____25355 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____25355);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____25398  ->
                                              match uu____25398 with
                                              | (env1,goal,opts) ->
                                                  let uu____25414 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____25414, opts)))))
                              else
                                (let uu____25416 =
                                   let uu____25423 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____25423)  in
                                 [uu____25416])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25456  ->
                                    match uu____25456 with
                                    | (env1,goal,opts) ->
                                        let uu____25466 = check_trivial goal
                                           in
                                        (match uu____25466 with
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
                                                (let uu____25474 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25475 =
                                                   let uu____25476 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25477 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25476 uu____25477
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25474 uu____25475)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25480 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25481 =
                                                   let uu____25482 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25482
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25480 uu____25481)
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
      let uu____25496 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25496 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____25503 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____25503
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25514 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____25514 with
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
          let uu____25542 = FStar_Syntax_Unionfind.find u  in
          match uu____25542 with
          | FStar_Pervasives_Native.None  -> true
          | uu____25545 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____25567 = acc  in
          match uu____25567 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____25653 = hd1  in
                   (match uu____25653 with
                    | (uu____25666,env,u,tm,k,r) ->
                        let uu____25672 = unresolved u  in
                        if uu____25672
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___200_25702 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___200_25702.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___200_25702.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___200_25702.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___200_25702.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___200_25702.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___200_25702.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___200_25702.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___200_25702.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___200_25702.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___200_25702.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___200_25702.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___200_25702.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___200_25702.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___200_25702.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___200_25702.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___200_25702.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___200_25702.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___200_25702.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___200_25702.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___200_25702.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___200_25702.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___200_25702.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___200_25702.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___200_25702.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___200_25702.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___200_25702.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___200_25702.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___200_25702.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___200_25702.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___200_25702.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___200_25702.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___200_25702.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___200_25702.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___200_25702.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___200_25702.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___200_25702.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____25705 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____25705
                            then
                              let uu____25706 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____25707 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____25708 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____25706 uu____25707 uu____25708
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e when FStar_Errors.handleable e ->
                                  ((let uu____25719 =
                                      let uu____25728 =
                                        let uu____25735 =
                                          let uu____25736 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____25737 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____25736 uu____25737
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____25735, r)
                                         in
                                      [uu____25728]  in
                                    FStar_Errors.add_errors uu____25719);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___203_25751 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___203_25751.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___203_25751.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___203_25751.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____25754 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25761  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____25754 with
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
        let uu___204_25789 = g  in
        let uu____25790 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___204_25789.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___204_25789.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___204_25789.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25790
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
        let uu____25852 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25852 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25865 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____25865
      | (reason,uu____25867,uu____25868,e,t,r)::uu____25872 ->
          let uu____25899 =
            let uu____25904 =
              let uu____25905 = FStar_Syntax_Print.term_to_string t  in
              let uu____25906 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25905 uu____25906
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25904)
             in
          FStar_Errors.raise_error uu____25899 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___205_25917 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___205_25917.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___205_25917.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___205_25917.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25944 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25944 with
      | FStar_Pervasives_Native.Some uu____25950 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25966 = try_teq false env t1 t2  in
        match uu____25966 with
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
        (let uu____25992 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25992
         then
           let uu____25993 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25994 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25993
             uu____25994
         else ());
        (let uu____25996 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25996 with
         | (prob,x) ->
             let g =
               let uu____26012 =
                 let uu____26015 = singleton' env prob true  in
                 solve_and_commit env uu____26015
                   (fun uu____26017  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26012  in
             ((let uu____26027 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26027
               then
                 let uu____26028 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26029 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26030 =
                   let uu____26031 = FStar_Util.must g  in
                   guard_to_string env uu____26031  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26028 uu____26029 uu____26030
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
        let uu____26065 = check_subtyping env t1 t2  in
        match uu____26065 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26084 =
              let uu____26085 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____26085 g  in
            FStar_Pervasives_Native.Some uu____26084
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26103 = check_subtyping env t1 t2  in
        match uu____26103 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26122 =
              let uu____26123 =
                let uu____26124 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26124]  in
              close_guard env uu____26123 g  in
            FStar_Pervasives_Native.Some uu____26122
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26141 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26141
         then
           let uu____26142 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26143 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26142
             uu____26143
         else ());
        (let uu____26145 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____26145 with
         | (prob,x) ->
             let g =
               let uu____26155 =
                 let uu____26158 = singleton' env prob false  in
                 solve_and_commit env uu____26158
                   (fun uu____26160  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26155  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26171 =
                      let uu____26172 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26172]  in
                    close_guard env uu____26171 g1  in
                  discharge_guard_nosmt env g2))
  