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
          let uu___118_101 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___118_101.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_101.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_101.FStar_TypeChecker_Env.implicits)
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
          let uu___119_247 = g  in
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
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____249
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____248;
            FStar_TypeChecker_Env.deferred =
              (uu___119_247.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___119_247.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___119_247.FStar_TypeChecker_Env.implicits)
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
          let uu___120_298 = g  in
          let uu____299 =
            let uu____300 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____300  in
          {
            FStar_TypeChecker_Env.guard_f = uu____299;
            FStar_TypeChecker_Env.deferred =
              (uu___120_298.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___120_298.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___120_298.FStar_TypeChecker_Env.implicits)
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
            let uu___121_456 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___121_456.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___121_456.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___121_456.FStar_TypeChecker_Env.implicits)
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
            let uu___122_500 = g  in
            let uu____501 =
              let uu____502 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____502  in
            {
              FStar_TypeChecker_Env.guard_f = uu____501;
              FStar_TypeChecker_Env.deferred =
                (uu___122_500.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___122_500.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___122_500.FStar_TypeChecker_Env.implicits)
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
  tcenv: FStar_TypeChecker_Env.env }[@@deriving show]
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
  | INVARIANT [@@deriving show]
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
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob = (FStar_Syntax_Syntax.comp,unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___88_952  ->
    match uu___88_952 with
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
    fun uu___89_1055  ->
      match uu___89_1055 with
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
    fun uu___90_1093  ->
      match uu___90_1093 with
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
        let uu___123_1230 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___123_1230.wl_deferred);
          ctr = (uu___123_1230.ctr);
          defer_ok = (uu___123_1230.defer_ok);
          smt_ok;
          tcenv = (uu___123_1230.tcenv)
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
      let uu___124_1270 = empty_worklist env  in
      let uu____1271 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1271;
        wl_deferred = (uu___124_1270.wl_deferred);
        ctr = (uu___124_1270.ctr);
        defer_ok = false;
        smt_ok = (uu___124_1270.smt_ok);
        tcenv = (uu___124_1270.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___125_1291 = wl  in
        {
          attempting = (uu___125_1291.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___125_1291.ctr);
          defer_ok = (uu___125_1291.defer_ok);
          smt_ok = (uu___125_1291.smt_ok);
          tcenv = (uu___125_1291.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___126_1312 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___126_1312.wl_deferred);
        ctr = (uu___126_1312.ctr);
        defer_ok = (uu___126_1312.defer_ok);
        smt_ok = (uu___126_1312.smt_ok);
        tcenv = (uu___126_1312.tcenv)
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
  fun uu___91_1336  ->
    match uu___91_1336 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1343 'Auu____1344 .
    ('Auu____1343,'Auu____1344) FStar_TypeChecker_Common.problem ->
      ('Auu____1343,'Auu____1344) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___127_1362 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___127_1362.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___127_1362.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___127_1362.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___127_1362.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___127_1362.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___127_1362.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___127_1362.FStar_TypeChecker_Common.rank)
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
  fun uu___92_1397  ->
    match uu___92_1397 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___93_1425  ->
      match uu___93_1425 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___94_1430  ->
    match uu___94_1430 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___95_1445  ->
    match uu___95_1445 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___96_1462  ->
    match uu___96_1462 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___97_1479  ->
    match uu___97_1479 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___98_1498  ->
    match uu___98_1498 with
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
  fun uu___99_1733  ->
    match uu___99_1733 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
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
         (fun uu___100_2168  ->
            match uu___100_2168 with
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
        (fun uu___101_2207  ->
           match uu___101_2207 with
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
        (fun uu___102_2246  ->
           match uu___102_2246 with
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
                    let uu___128_2355 = x  in
                    let uu____2356 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___128_2355.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___128_2355.FStar_Syntax_Syntax.index);
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
                  (let uu___129_3804 = wl  in
                   {
                     attempting = (uu___129_3804.attempting);
                     wl_deferred = (uu___129_3804.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___129_3804.defer_ok);
                     smt_ok = (uu___129_3804.smt_ok);
                     tcenv = (uu___129_3804.tcenv)
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
        (let uu___130_3835 = wl  in
         {
           attempting = (uu___130_3835.attempting);
           wl_deferred = (uu___130_3835.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___130_3835.defer_ok);
           smt_ok = (uu___130_3835.smt_ok);
           tcenv = (uu___130_3835.tcenv)
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
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5461 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5498 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5504 -> false
  
let string_of_option :
  'Auu____5511 .
    ('Auu____5511 -> Prims.string) ->
      'Auu____5511 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___103_5526  ->
      match uu___103_5526 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5532 = f x  in Prims.strcat "Some " uu____5532
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___104_5537  ->
    match uu___104_5537 with
    | MisMatch (d1,d2) ->
        let uu____5548 =
          let uu____5549 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5550 =
            let uu____5551 =
              let uu____5552 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5552 ")"  in
            Prims.strcat ") (" uu____5551  in
          Prims.strcat uu____5549 uu____5550  in
        Prims.strcat "MisMatch (" uu____5548
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___105_5557  ->
    match uu___105_5557 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5572 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5602 = m2 ()  in
          (match uu____5602 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5617 -> HeadMatch)
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
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____5631 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5631 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5642 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5665 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5674 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5702 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5702
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5703 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5704 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5705 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5722 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5735 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5759) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5765,uu____5766) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5808) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5829;
             FStar_Syntax_Syntax.index = uu____5830;
             FStar_Syntax_Syntax.sort = t2;_},uu____5832)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5839 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5840 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5841 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5854 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5861 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5879 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5879
  
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
            let uu____5906 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5906
            then FullMatch
            else
              (let uu____5908 =
                 let uu____5917 =
                   let uu____5920 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5920  in
                 let uu____5921 =
                   let uu____5924 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5924  in
                 (uu____5917, uu____5921)  in
               MisMatch uu____5908)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5930),FStar_Syntax_Syntax.Tm_uinst (g,uu____5932)) ->
            let uu____5941 = head_matches env f g  in
            FStar_All.pipe_right uu____5941 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5944 = FStar_Const.eq_const c d  in
            if uu____5944
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5951),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5953)) ->
            let uu____6002 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____6002
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6009),FStar_Syntax_Syntax.Tm_refine (y,uu____6011)) ->
            let uu____6020 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6020 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6022),uu____6023) ->
            let uu____6028 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6028 head_match
        | (uu____6029,FStar_Syntax_Syntax.Tm_refine (x,uu____6031)) ->
            let uu____6036 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6036 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6037,FStar_Syntax_Syntax.Tm_type
           uu____6038) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6039,FStar_Syntax_Syntax.Tm_arrow uu____6040) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6066),FStar_Syntax_Syntax.Tm_app (head',uu____6068))
            ->
            let uu____6109 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6109 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6111),uu____6112) ->
            let uu____6133 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6133 head_match
        | (uu____6134,FStar_Syntax_Syntax.Tm_app (head1,uu____6136)) ->
            let uu____6157 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6157 head_match
        | uu____6158 ->
            let uu____6163 =
              let uu____6172 = delta_depth_of_term env t11  in
              let uu____6175 = delta_depth_of_term env t21  in
              (uu____6172, uu____6175)  in
            MisMatch uu____6163
  
let head_matches_delta :
  'Auu____6192 .
    FStar_TypeChecker_Env.env ->
      'Auu____6192 ->
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
            let uu____6231 = FStar_Syntax_Util.head_and_args t  in
            match uu____6231 with
            | (head1,uu____6249) ->
                let uu____6270 =
                  let uu____6271 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6271.FStar_Syntax_Syntax.n  in
                (match uu____6270 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6277 =
                       let uu____6278 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6278 FStar_Option.isSome
                        in
                     if uu____6277
                     then
                       let uu____6297 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6297
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6301 -> FStar_Pervasives_Native.None)
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
            let reduce_one_and_try_again d1 d2 =
              let d1_greater_than_d2 =
                FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
              let uu____6434 =
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
              match uu____6434 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____6479 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____6479 with
              | FStar_Pervasives_Native.None  -> fail1 r1
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
                ((i > (Prims.parse_int "1")) || (j > (Prims.parse_int "1")))
                  && (i <> j)
                ->
                reduce_one_and_try_again
                  (FStar_Syntax_Syntax.Delta_equational_at_level i)
                  (FStar_Syntax_Syntax.Delta_equational_at_level j)
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level
                 uu____6511),uu____6512)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6530 =
                     let uu____6539 = maybe_inline t11  in
                     let uu____6542 = maybe_inline t21  in
                     (uu____6539, uu____6542)  in
                   match uu____6530 with
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
                (uu____6579,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6580))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6598 =
                     let uu____6607 = maybe_inline t11  in
                     let uu____6610 = maybe_inline t21  in
                     (uu____6607, uu____6610)  in
                   match uu____6598 with
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
                when d1 = d2 -> reduce_both_and_try_again d1 r
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                -> reduce_one_and_try_again d1 d2
            | MisMatch uu____6659 -> fail1 r
            | uu____6668 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6681 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6681
           then
             let uu____6682 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6683 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6684 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6691 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6709 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6709
                    (fun uu____6743  ->
                       match uu____6743 with
                       | (t11,t21) ->
                           let uu____6750 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6751 =
                             let uu____6752 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6752  in
                           Prims.strcat uu____6750 uu____6751))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____6682
               uu____6683 uu____6684 uu____6691
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6792 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6836 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___106_6850  ->
    match uu___106_6850 with
    | T (t,uu____6852) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6876 = FStar_Syntax_Util.type_u ()  in
      match uu____6876 with
      | (t,uu____6882) ->
          let uu____6883 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6883
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6898 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6898 FStar_Pervasives_Native.fst
  
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
        let uu____6972 = head_matches env t1 t'  in
        match uu____6972 with
        | MisMatch uu____6973 -> false
        | uu____6982 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____7082,imp),T (t2,uu____7085)) -> (t2, imp)
                     | uu____7108 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7175  ->
                    match uu____7175 with
                    | (t2,uu____7189) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7236 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7236 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7321))::tcs2) ->
                       aux
                         (((let uu___131_7360 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_7360.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_7360.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7378 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___107_7435 =
                 match uu___107_7435 with
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
               let uu____7554 = decompose1 [] bs1  in
               (rebuild, matches, uu____7554))
      | uu____7605 ->
          let rebuild uu___108_7613 =
            match uu___108_7613 with
            | [] -> t1
            | uu____7616 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___109_7651  ->
    match uu___109_7651 with
    | T (t,uu____7653) -> t
    | uu____7666 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___110_7671  ->
    match uu___110_7671 with
    | T (t,uu____7673) -> FStar_Syntax_Syntax.as_arg t
    | uu____7686 -> failwith "Impossible"
  
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
              | (uu____7818,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7847 = new_uvar r scope1 k  in
                  (match uu____7847 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7865 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7882 =
                         let uu____7883 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_23  ->
                              FStar_TypeChecker_Common.TProb _0_23)
                           uu____7883
                          in
                       ((T (gi_xs, mk_kind)), uu____7882))
              | (uu____7898,uu____7899,C uu____7900) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____8053 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8070;
                         FStar_Syntax_Syntax.vars = uu____8071;_})
                        ->
                        let uu____8094 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8094 with
                         | (T (gi_xs,uu____8120),prob) ->
                             let uu____8134 =
                               let uu____8135 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_24  -> C _0_24)
                                 uu____8135
                                in
                             (uu____8134, [prob])
                         | uu____8138 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8153;
                         FStar_Syntax_Syntax.vars = uu____8154;_})
                        ->
                        let uu____8177 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8177 with
                         | (T (gi_xs,uu____8203),prob) ->
                             let uu____8217 =
                               let uu____8218 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_25  -> C _0_25)
                                 uu____8218
                                in
                             (uu____8217, [prob])
                         | uu____8221 -> failwith "impossible")
                    | (uu____8232,uu____8233,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8235;
                         FStar_Syntax_Syntax.vars = uu____8236;_})
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
                        let uu____8371 =
                          let uu____8380 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8380 FStar_List.unzip
                           in
                        (match uu____8371 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8434 =
                                 let uu____8435 =
                                   let uu____8438 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8438 un_T  in
                                 let uu____8439 =
                                   let uu____8448 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8448
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8435;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8439;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8434
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8457 ->
                        let uu____8470 = sub_prob scope1 args q  in
                        (match uu____8470 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____8053 with
                   | (tc,probs) ->
                       let uu____8501 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8564,uu____8565),T
                            (t,uu____8567)) ->
                             let b1 =
                               ((let uu___132_8608 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___132_8608.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___132_8608.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8609 =
                               let uu____8616 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8616 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8609)
                         | uu____8651 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8501 with
                        | (bopt,scope2,args1) ->
                            let uu____8735 = aux scope2 args1 qs2  in
                            (match uu____8735 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8773 =
                                           let uu____8776 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8776  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8773
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
                                         let uu____8801 =
                                           let uu____8804 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8805 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8804 :: uu____8805  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8801
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
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4[@@deriving show]
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
    FStar_Pervasives_Native.tuple3[@@deriving show]
let (rigid_rigid : Prims.int) = (Prims.parse_int "0") 
let (flex_rigid_eq : Prims.int) = (Prims.parse_int "1") 
let (flex_refine_inner : Prims.int) = (Prims.parse_int "2") 
let (flex_refine : Prims.int) = (Prims.parse_int "3") 
let (flex_rigid : Prims.int) = (Prims.parse_int "4") 
let (rigid_flex : Prims.int) = (Prims.parse_int "5") 
let (refine_flex : Prims.int) = (Prims.parse_int "6") 
let (flex_flex : Prims.int) = (Prims.parse_int "7") 
let compress_tprob :
  'Auu____8879 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8879)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8879)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___133_8902 = p  in
      let uu____8907 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8908 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___133_8902.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8907;
        FStar_TypeChecker_Common.relation =
          (uu___133_8902.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8908;
        FStar_TypeChecker_Common.element =
          (uu___133_8902.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___133_8902.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___133_8902.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___133_8902.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___133_8902.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___133_8902.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8924 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8924
            (fun _0_26  -> FStar_TypeChecker_Common.TProb _0_26)
      | FStar_TypeChecker_Common.CProb uu____8933 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8957 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8957 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8967 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8967 with
           | (lh,uu____8987) ->
               let uu____9008 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9008 with
                | (rh,uu____9028) ->
                    let uu____9049 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9066,FStar_Syntax_Syntax.Tm_uvar uu____9067)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9104,uu____9105)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9126,FStar_Syntax_Syntax.Tm_uvar uu____9127)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9148,uu____9149)
                          ->
                          let uu____9166 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9166 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9215 ->
                                    let rank =
                                      let uu____9223 = is_top_level_prob prob
                                         in
                                      if uu____9223
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9225 =
                                      let uu___134_9230 = tp  in
                                      let uu____9235 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___134_9230.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___134_9230.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___134_9230.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9235;
                                        FStar_TypeChecker_Common.element =
                                          (uu___134_9230.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___134_9230.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___134_9230.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___134_9230.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___134_9230.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___134_9230.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9225)))
                      | (uu____9246,FStar_Syntax_Syntax.Tm_uvar uu____9247)
                          ->
                          let uu____9264 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9264 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9313 ->
                                    let uu____9320 =
                                      let uu___135_9327 = tp  in
                                      let uu____9332 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_9327.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9332;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_9327.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___135_9327.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_9327.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_9327.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_9327.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_9327.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_9327.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_9327.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9320)))
                      | (uu____9349,uu____9350) -> (rigid_rigid, tp)  in
                    (match uu____9049 with
                     | (rank,tp1) ->
                         let uu____9369 =
                           FStar_All.pipe_right
                             (let uu___136_9375 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___136_9375.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___136_9375.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___136_9375.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___136_9375.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___136_9375.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___136_9375.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___136_9375.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___136_9375.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___136_9375.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_27  ->
                                FStar_TypeChecker_Common.TProb _0_27)
                            in
                         (rank, uu____9369))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9385 =
            FStar_All.pipe_right
              (let uu___137_9391 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_9391.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_9391.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_9391.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_9391.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_9391.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_9391.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___137_9391.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_9391.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_9391.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_28  -> FStar_TypeChecker_Common.CProb _0_28)
             in
          (rigid_rigid, uu____9385)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9452 probs =
      match uu____9452 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9505 = rank wl hd1  in
               (match uu____9505 with
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
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9621 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9635 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9649 -> false
  
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
                        let uu____9701 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9701 with
                        | (k,uu____9707) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9717 -> false)))
            | uu____9718 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9770 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9776 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9776 = (Prims.parse_int "0")))
                           in
                        if uu____9770 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9792 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9798 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9798 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9792)
               in
            let uu____9799 = filter1 u12  in
            let uu____9802 = filter1 u22  in (uu____9799, uu____9802)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9831 = filter_out_common_univs us1 us2  in
                (match uu____9831 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9890 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9890 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9893 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9903 =
                          let uu____9904 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9905 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9904
                            uu____9905
                           in
                        UFailed uu____9903))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9929 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9929 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9955 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9955 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9958 ->
                let uu____9963 =
                  let uu____9964 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9965 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9964
                    uu____9965 msg
                   in
                UFailed uu____9963
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9966,uu____9967) ->
              let uu____9968 =
                let uu____9969 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9970 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9969 uu____9970
                 in
              failwith uu____9968
          | (FStar_Syntax_Syntax.U_unknown ,uu____9971) ->
              let uu____9972 =
                let uu____9973 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9974 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9973 uu____9974
                 in
              failwith uu____9972
          | (uu____9975,FStar_Syntax_Syntax.U_bvar uu____9976) ->
              let uu____9977 =
                let uu____9978 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9979 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9978 uu____9979
                 in
              failwith uu____9977
          | (uu____9980,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9981 =
                let uu____9982 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9983 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9982 uu____9983
                 in
              failwith uu____9981
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10007 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10007
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10029 = occurs_univ v1 u3  in
              if uu____10029
              then
                let uu____10030 =
                  let uu____10031 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10032 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10031 uu____10032
                   in
                try_umax_components u11 u21 uu____10030
              else
                (let uu____10034 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10034)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10054 = occurs_univ v1 u3  in
              if uu____10054
              then
                let uu____10055 =
                  let uu____10056 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10057 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10056 uu____10057
                   in
                try_umax_components u11 u21 uu____10055
              else
                (let uu____10059 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10059)
          | (FStar_Syntax_Syntax.U_max uu____10068,uu____10069) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10075 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10075
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10077,FStar_Syntax_Syntax.U_max uu____10078) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10084 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10084
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10086,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10087,FStar_Syntax_Syntax.U_name uu____10088) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10089) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10090) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10091,FStar_Syntax_Syntax.U_succ uu____10092) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10093,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10193 = bc1  in
      match uu____10193 with
      | (bs1,mk_cod1) ->
          let uu____10237 = bc2  in
          (match uu____10237 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10348 = aux xs ys  in
                     (match uu____10348 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10431 =
                       let uu____10438 = mk_cod1 xs  in ([], uu____10438)  in
                     let uu____10441 =
                       let uu____10448 = mk_cod2 ys  in ([], uu____10448)  in
                     (uu____10431, uu____10441)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10633 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10633
       then
         let uu____10634 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10634
       else ());
      (let uu____10636 = next_prob probs  in
       match uu____10636 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___138_10657 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___138_10657.wl_deferred);
               ctr = (uu___138_10657.ctr);
               defer_ok = (uu___138_10657.defer_ok);
               smt_ok = (uu___138_10657.smt_ok);
               tcenv = (uu___138_10657.tcenv)
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
                  let uu____10668 = solve_flex_rigid_join env tp probs1  in
                  (match uu____10668 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10673 = solve_rigid_flex_meet env tp probs1
                        in
                     match uu____10673 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10678,uu____10679) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10696 ->
                let uu____10705 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10764  ->
                          match uu____10764 with
                          | (c,uu____10772,uu____10773) -> c < probs.ctr))
                   in
                (match uu____10705 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10814 =
                            FStar_List.map
                              (fun uu____10829  ->
                                 match uu____10829 with
                                 | (uu____10840,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10814
                      | uu____10843 ->
                          let uu____10852 =
                            let uu___139_10853 = probs  in
                            let uu____10854 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10875  ->
                                      match uu____10875 with
                                      | (uu____10882,uu____10883,y) -> y))
                               in
                            {
                              attempting = uu____10854;
                              wl_deferred = rest;
                              ctr = (uu___139_10853.ctr);
                              defer_ok = (uu___139_10853.defer_ok);
                              smt_ok = (uu___139_10853.smt_ok);
                              tcenv = (uu___139_10853.tcenv)
                            }  in
                          solve env uu____10852))))

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
            let uu____10890 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10890 with
            | USolved wl1 ->
                let uu____10892 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10892
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
                  let uu____10944 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10944 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10947 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10959;
                  FStar_Syntax_Syntax.vars = uu____10960;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10963;
                  FStar_Syntax_Syntax.vars = uu____10964;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10976,uu____10977) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10984,FStar_Syntax_Syntax.Tm_uinst uu____10985) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10992 -> USolved wl

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
            ((let uu____11002 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11002
              then
                let uu____11003 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11003 msg
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
        (let uu____11012 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11012
         then
           let uu____11013 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____11013
         else ());
        (let uu____11015 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____11015 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____11081 = head_matches_delta env () t1 t2  in
               match uu____11081 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____11122 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____11171 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____11186 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____11187 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____11186, uu____11187)
                          | FStar_Pervasives_Native.None  ->
                              let uu____11192 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____11193 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____11192, uu____11193)
                           in
                        (match uu____11171 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11223 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_29  ->
                                    FStar_TypeChecker_Common.TProb _0_29)
                                 uu____11223
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11254 =
                                    let uu____11263 =
                                      let uu____11266 =
                                        let uu____11273 =
                                          let uu____11274 =
                                            let uu____11281 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____11281)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11274
                                           in
                                        FStar_Syntax_Syntax.mk uu____11273
                                         in
                                      uu____11266
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____11289 =
                                      let uu____11292 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____11292]  in
                                    (uu____11263, uu____11289)  in
                                  FStar_Pervasives_Native.Some uu____11254
                              | (uu____11305,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11307)) ->
                                  let uu____11312 =
                                    let uu____11319 =
                                      let uu____11322 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____11322]  in
                                    (t11, uu____11319)  in
                                  FStar_Pervasives_Native.Some uu____11312
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11332),uu____11333) ->
                                  let uu____11338 =
                                    let uu____11345 =
                                      let uu____11348 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____11348]  in
                                    (t21, uu____11345)  in
                                  FStar_Pervasives_Native.Some uu____11338
                              | uu____11357 ->
                                  let uu____11362 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____11362 with
                                   | (head1,uu____11386) ->
                                       let uu____11407 =
                                         let uu____11408 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____11408.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____11407 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11419;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11421;_}
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
                                        | uu____11428 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11441) ->
                  let uu____11466 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___111_11492  ->
                            match uu___111_11492 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11499 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____11499 with
                                      | (u',uu____11515) ->
                                          let uu____11536 =
                                            let uu____11537 = whnf env u'  in
                                            uu____11537.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11536 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11541) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11566 -> false))
                                 | uu____11567 -> false)
                            | uu____11570 -> false))
                     in
                  (match uu____11466 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11608 tps =
                         match uu____11608 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11656 =
                                    let uu____11665 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____11665  in
                                  (match uu____11656 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11700 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11709 =
                         let uu____11718 =
                           let uu____11725 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11725, [])  in
                         make_lower_bound uu____11718 lower_bounds  in
                       (match uu____11709 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11737 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11737
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
                            ((let uu____11757 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11757
                              then
                                let wl' =
                                  let uu___140_11759 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___140_11759.wl_deferred);
                                    ctr = (uu___140_11759.ctr);
                                    defer_ok = (uu___140_11759.defer_ok);
                                    smt_ok = (uu___140_11759.smt_ok);
                                    tcenv = (uu___140_11759.tcenv)
                                  }  in
                                let uu____11760 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11760
                              else ());
                             (let uu____11762 =
                                solve_t env eq_prob
                                  (let uu___141_11764 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___141_11764.wl_deferred);
                                     ctr = (uu___141_11764.ctr);
                                     defer_ok = (uu___141_11764.defer_ok);
                                     smt_ok = (uu___141_11764.smt_ok);
                                     tcenv = (uu___141_11764.tcenv)
                                   })
                                 in
                              match uu____11762 with
                              | Success uu____11767 ->
                                  let wl1 =
                                    let uu___142_11769 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___142_11769.wl_deferred);
                                      ctr = (uu___142_11769.ctr);
                                      defer_ok = (uu___142_11769.defer_ok);
                                      smt_ok = (uu___142_11769.smt_ok);
                                      tcenv = (uu___142_11769.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11771 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11776 -> FStar_Pervasives_Native.None))))
              | uu____11777 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11786 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11786
         then
           let uu____11787 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11787
         else ());
        (let uu____11789 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11789 with
         | (u,args) ->
             let uu____11828 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11828 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____11877 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____11877 with
                    | (h1,args1) ->
                        let uu____11918 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11918 with
                         | (h2,uu____11938) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11965 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11965
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11983 =
                                          let uu____11986 =
                                            let uu____11987 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_30  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_30) uu____11987
                                             in
                                          [uu____11986]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11983))
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
                                       (let uu____12020 =
                                          let uu____12023 =
                                            let uu____12024 =
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
                                                   _0_31) uu____12024
                                             in
                                          [uu____12023]  in
                                        FStar_Pervasives_Native.Some
                                          uu____12020))
                                  else FStar_Pervasives_Native.None
                              | uu____12038 -> FStar_Pervasives_Native.None))
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
                             let uu____12132 =
                               let uu____12141 =
                                 let uu____12144 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____12144  in
                               (uu____12141, m1)  in
                             FStar_Pervasives_Native.Some uu____12132)
                    | (uu____12157,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12159)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12207),uu____12208) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12255 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12308) ->
                       let uu____12333 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___112_12359  ->
                                 match uu___112_12359 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12366 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____12366 with
                                           | (u',uu____12382) ->
                                               let uu____12403 =
                                                 let uu____12404 =
                                                   whnf env u'  in
                                                 uu____12404.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____12403 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12408) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12433 -> false))
                                      | uu____12434 -> false)
                                 | uu____12437 -> false))
                          in
                       (match uu____12333 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12479 tps =
                              match uu____12479 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12541 =
                                         let uu____12552 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____12552  in
                                       (match uu____12541 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12603 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____12614 =
                              let uu____12625 =
                                let uu____12634 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____12634, [])  in
                              make_upper_bound uu____12625 upper_bounds  in
                            (match uu____12614 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12648 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12648
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
                                 ((let uu____12674 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12674
                                   then
                                     let wl' =
                                       let uu___143_12676 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___143_12676.wl_deferred);
                                         ctr = (uu___143_12676.ctr);
                                         defer_ok = (uu___143_12676.defer_ok);
                                         smt_ok = (uu___143_12676.smt_ok);
                                         tcenv = (uu___143_12676.tcenv)
                                       }  in
                                     let uu____12677 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12677
                                   else ());
                                  (let uu____12679 =
                                     solve_t env eq_prob
                                       (let uu___144_12681 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___144_12681.wl_deferred);
                                          ctr = (uu___144_12681.ctr);
                                          defer_ok =
                                            (uu___144_12681.defer_ok);
                                          smt_ok = (uu___144_12681.smt_ok);
                                          tcenv = (uu___144_12681.tcenv)
                                        })
                                      in
                                   match uu____12679 with
                                   | Success uu____12684 ->
                                       let wl1 =
                                         let uu___145_12686 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___145_12686.wl_deferred);
                                           ctr = (uu___145_12686.ctr);
                                           defer_ok =
                                             (uu___145_12686.defer_ok);
                                           smt_ok = (uu___145_12686.smt_ok);
                                           tcenv = (uu___145_12686.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____12688 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12693 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12694 -> failwith "Impossible: Not a flex-rigid")))

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
              (let uu____12712 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12712
               then
                 let uu____12713 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12714 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12713 (rel_to_string (p_rel orig)) uu____12714
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____12784 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____12784
                       then
                         let uu____12785 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____12785
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___146_12839 = hd1  in
                       let uu____12840 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___146_12839.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___146_12839.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12840
                       }  in
                     let hd21 =
                       let uu___147_12844 = hd2  in
                       let uu____12845 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___147_12844.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___147_12844.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12845
                       }  in
                     let prob =
                       let uu____12849 =
                         let uu____12854 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____12854 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
                         uu____12849
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____12865 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____12865
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____12869 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____12869 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____12907 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____12912 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____12907 uu____12912
                             in
                          ((let uu____12922 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12922
                            then
                              let uu____12923 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____12924 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____12923 uu____12924
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____12947 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____12957 = aux scope env [] bs1 bs2  in
               match uu____12957 with
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
        (let uu____12982 = compress_tprob wl problem  in
         solve_t' env uu____12982 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____13034 = head_matches_delta env1 wl1 t1 t2  in
           match uu____13034 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____13065,uu____13066) ->
                    let rec may_relate head3 =
                      let uu____13093 =
                        let uu____13094 = FStar_Syntax_Subst.compress head3
                           in
                        uu____13094.FStar_Syntax_Syntax.n  in
                      match uu____13093 with
                      | FStar_Syntax_Syntax.Tm_name uu____13097 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____13098 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13121;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____13122;
                            FStar_Syntax_Syntax.fv_qual = uu____13123;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13126;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13127;
                            FStar_Syntax_Syntax.fv_qual = uu____13128;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13132,uu____13133) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13175) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13181) ->
                          may_relate t
                      | uu____13186 -> false  in
                    let uu____13187 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13187
                    then
                      let guard =
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then mk_eq2 orig t1 t2
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
                                 let uu____13208 =
                                   let uu____13209 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13209 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13208
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____13211 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____13211
                    else
                      (let uu____13213 =
                         let uu____13214 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13215 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13214 uu____13215
                          in
                       giveup env1 uu____13213 orig)
                | (uu____13216,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___148_13230 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_13230.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_13230.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___148_13230.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_13230.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_13230.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_13230.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_13230.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_13230.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13231,FStar_Pervasives_Native.None ) ->
                    ((let uu____13243 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13243
                      then
                        let uu____13244 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13245 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13246 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13247 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____13244 uu____13245 uu____13246 uu____13247
                      else ());
                     (let uu____13249 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13249 with
                      | (head11,args1) ->
                          let uu____13286 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13286 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____13340 =
                                   let uu____13341 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____13342 = args_to_string args1  in
                                   let uu____13343 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____13344 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____13341 uu____13342 uu____13343
                                     uu____13344
                                    in
                                 giveup env1 uu____13340 orig
                               else
                                 (let uu____13346 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____13352 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____13352 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____13346
                                  then
                                    let uu____13353 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____13353 with
                                    | USolved wl2 ->
                                        let uu____13355 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____13355
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____13359 =
                                       base_and_refinement env1 t1  in
                                     match uu____13359 with
                                     | (base1,refinement1) ->
                                         let uu____13384 =
                                           base_and_refinement env1 t2  in
                                         (match uu____13384 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13441 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13441 with
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
                                                            (fun uu____13463 
                                                               ->
                                                               fun
                                                                 uu____13464 
                                                                 ->
                                                                 match 
                                                                   (uu____13463,
                                                                    uu____13464)
                                                                 with
                                                                 | ((a,uu____13482),
                                                                    (a',uu____13484))
                                                                    ->
                                                                    let uu____13493
                                                                    =
                                                                    let uu____13498
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____13498
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_33  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_33)
                                                                    uu____13493)
                                                            args1 args2
                                                           in
                                                        ((let uu____13504 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env1)
                                                              (FStar_Options.Other
                                                                 "Rel")
                                                             in
                                                          if uu____13504
                                                          then
                                                            let uu____13505 =
                                                              FStar_Syntax_Print.list_to_string
                                                                (prob_to_string
                                                                   env1)
                                                                subprobs
                                                               in
                                                            FStar_Util.print1
                                                              "Adding subproblems for arguments: %s"
                                                              uu____13505
                                                          else ());
                                                         (let formula =
                                                            let uu____13508 =
                                                              FStar_List.map
                                                                (fun p  ->
                                                                   FStar_Pervasives_Native.fst
                                                                    (p_guard
                                                                    p))
                                                                subprobs
                                                               in
                                                            FStar_Syntax_Util.mk_conj_l
                                                              uu____13508
                                                             in
                                                          let wl3 =
                                                            solve_prob orig
                                                              (FStar_Pervasives_Native.Some
                                                                 formula) []
                                                              wl2
                                                             in
                                                          solve env1
                                                            (attempt subprobs
                                                               wl3))))
                                               | uu____13514 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___149_13550 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___149_13550.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____13587 =
           match uu____13587 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____13631 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____13631 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____13743  ->
                      let uu____13744 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____13744);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____13812  ->
                                match uu____13812 with
                                | (x,imp) ->
                                    let uu____13823 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____13823, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____13836 = FStar_Syntax_Util.type_u ()  in
                        match uu____13836 with
                        | (t1,uu____13842) ->
                            let uu____13843 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____13843
                         in
                      let uu____13848 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____13848 with
                       | (t',tm_u1) ->
                           let uu____13861 = destruct_flex_t t'  in
                           (match uu____13861 with
                            | (uu____13898,u1,k1,uu____13901) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____13960 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13960
                                   in
                                let sol =
                                  let uu____13964 =
                                    let uu____13973 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13973)  in
                                  TERM uu____13964  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____14108  ->
                            let uu____14109 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____14110 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____14109 uu____14110);
                       (let uu____14123 = pat_var_opt env pat_args hd1  in
                        match uu____14123 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____14143  ->
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
                                       (fun uu____14186  ->
                                          match uu____14186 with
                                          | (x,uu____14192) ->
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
                                 (fun uu____14207  ->
                                    let uu____14208 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____14221 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____14208
                                      uu____14221);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____14225 =
                                  let uu____14226 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____14226  in
                                if uu____14225
                                then
                                  (debug1
                                     (fun uu____14238  ->
                                        let uu____14239 =
                                          let uu____14242 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____14255 =
                                            let uu____14258 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____14259 =
                                              let uu____14262 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____14263 =
                                                let uu____14266 =
                                                  names_to_string fvs  in
                                                let uu____14267 =
                                                  let uu____14270 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____14270]  in
                                                uu____14266 :: uu____14267
                                                 in
                                              uu____14262 :: uu____14263  in
                                            uu____14258 :: uu____14259  in
                                          uu____14242 :: uu____14255  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____14239);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____14272 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____14275 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____14272 (formal ::
                                     pattern_vars) uu____14275 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____14282::uu____14283) ->
                      let uu____14314 =
                        let uu____14327 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____14327  in
                      (match uu____14314 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____14366 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____14373::uu____14374,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____14397 =
                 let uu____14410 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____14410  in
               (match uu____14397 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____14446  ->
                          let uu____14447 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14448 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14449 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14450 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14447 uu____14448 uu____14449 uu____14450);
                     (let uu____14451 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____14454 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____14451 [] uu____14454 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____14500 = lhs  in
           match uu____14500 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____14510 ->
                     let uu____14511 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____14511 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____14542 = p  in
           match uu____14542 with
           | (((u,k),xs,c),ps,(h,uu____14553,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14641 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____14641 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____14664 = h gs_xs  in
                      let uu____14665 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                         in
                      FStar_Syntax_Util.abs xs1 uu____14664 uu____14665  in
                    ((let uu____14671 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14671
                      then
                        let uu____14672 =
                          let uu____14675 =
                            let uu____14676 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____14676
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____14681 =
                            let uu____14684 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____14685 =
                              let uu____14688 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____14689 =
                                let uu____14692 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____14693 =
                                  let uu____14696 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____14697 =
                                    let uu____14700 =
                                      let uu____14701 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____14701
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____14706 =
                                      let uu____14709 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____14709]  in
                                    uu____14700 :: uu____14706  in
                                  uu____14696 :: uu____14697  in
                                uu____14692 :: uu____14693  in
                              uu____14688 :: uu____14689  in
                            uu____14684 :: uu____14685  in
                          uu____14675 :: uu____14681  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____14672
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___113_14739 =
           match uu___113_14739 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____14781 = p  in
           match uu____14781 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14878 = FStar_List.nth ps i  in
               (match uu____14878 with
                | (pi,uu____14882) ->
                    let uu____14887 = FStar_List.nth xs i  in
                    (match uu____14887 with
                     | (xi,uu____14899) ->
                         let rec gs k =
                           let uu____14914 =
                             let uu____14927 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____14927  in
                           match uu____14914 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____15006)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____15019 = new_uvar r xs k_a  in
                                     (match uu____15019 with
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
                                          let uu____15041 = aux subst2 tl1
                                             in
                                          (match uu____15041 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____15068 =
                                                 let uu____15071 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____15071 :: gi_xs'  in
                                               let uu____15072 =
                                                 let uu____15075 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____15075 :: gi_ps'  in
                                               (uu____15068, uu____15072)))
                                  in
                               aux [] bs
                            in
                         let uu____15080 =
                           let uu____15081 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____15081
                            in
                         if uu____15080
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____15085 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____15085 with
                            | (g_xs,uu____15097) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____15108 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____15109 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_35  ->
                                         FStar_Pervasives_Native.Some _0_35)
                                     in
                                  FStar_Syntax_Util.abs xs uu____15108
                                    uu____15109
                                   in
                                let sub1 =
                                  let uu____15115 =
                                    let uu____15120 = p_scope orig  in
                                    let uu____15121 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____15124 =
                                      let uu____15127 =
                                        FStar_List.map
                                          (fun uu____15142  ->
                                             match uu____15142 with
                                             | (uu____15151,uu____15152,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____15127  in
                                    mk_problem uu____15120 orig uu____15121
                                      (p_rel orig) uu____15124
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_36  ->
                                       FStar_TypeChecker_Common.TProb _0_36)
                                    uu____15115
                                   in
                                ((let uu____15167 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15167
                                  then
                                    let uu____15168 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____15169 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____15168 uu____15169
                                  else ());
                                 (let wl2 =
                                    let uu____15172 =
                                      let uu____15175 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____15175
                                       in
                                    solve_prob orig uu____15172
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____15184 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_37  ->
                                       FStar_Pervasives_Native.Some _0_37)
                                    uu____15184)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____15225 = lhs  in
           match uu____15225 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____15263 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____15263 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____15296 =
                         let uu____15345 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____15345)  in
                       FStar_Pervasives_Native.Some uu____15296
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____15499 =
                            let uu____15506 =
                              let uu____15507 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____15507.FStar_Syntax_Syntax.n  in
                            (uu____15506, args)  in
                          match uu____15499 with
                          | (uu____15518,[]) ->
                              let uu____15521 =
                                let uu____15532 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____15532)  in
                              FStar_Pervasives_Native.Some uu____15521
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____15553,uu____15554) ->
                              let uu____15575 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15575 with
                               | (uv1,uv_args) ->
                                   let uu____15618 =
                                     let uu____15619 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15619.FStar_Syntax_Syntax.n  in
                                   (match uu____15618 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15629) ->
                                        let uu____15654 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15654 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15681  ->
                                                       let uu____15682 =
                                                         let uu____15683 =
                                                           let uu____15684 =
                                                             let uu____15689
                                                               =
                                                               let uu____15690
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15690
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15689
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15684
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15683
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15682))
                                                in
                                             let c1 =
                                               let uu____15700 =
                                                 let uu____15701 =
                                                   let uu____15706 =
                                                     let uu____15707 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15707
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15706
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15701
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15700
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15720 =
                                                 let uu____15723 =
                                                   let uu____15724 =
                                                     let uu____15727 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15727
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15724
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15723
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15720
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15746 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____15751,uu____15752) ->
                              let uu____15771 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15771 with
                               | (uv1,uv_args) ->
                                   let uu____15814 =
                                     let uu____15815 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15815.FStar_Syntax_Syntax.n  in
                                   (match uu____15814 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15825) ->
                                        let uu____15850 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15850 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15877  ->
                                                       let uu____15878 =
                                                         let uu____15879 =
                                                           let uu____15880 =
                                                             let uu____15885
                                                               =
                                                               let uu____15886
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15886
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15885
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15880
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15879
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15878))
                                                in
                                             let c1 =
                                               let uu____15896 =
                                                 let uu____15897 =
                                                   let uu____15902 =
                                                     let uu____15903 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15903
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15902
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15897
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15896
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15916 =
                                                 let uu____15919 =
                                                   let uu____15920 =
                                                     let uu____15923 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15923
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15920
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15919
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15916
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15942 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____15949) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____15990 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____15990
                                  (fun _0_38  ->
                                     FStar_Pervasives_Native.Some _0_38)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____16026 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____16026 with
                                   | (args1,rest) ->
                                       let uu____16055 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____16055 with
                                        | (xs2,c2) ->
                                            let uu____16068 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____16068
                                              (fun uu____16092  ->
                                                 match uu____16092 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____16132 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____16132 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16200 =
                                         let uu____16205 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____16205
                                          in
                                       FStar_All.pipe_right uu____16200
                                         (fun _0_39  ->
                                            FStar_Pervasives_Native.Some
                                              _0_39))
                          | uu____16220 ->
                              let uu____16227 =
                                let uu____16232 =
                                  let uu____16233 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____16234 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____16235 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____16233 uu____16234 uu____16235
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____16232)
                                 in
                              FStar_Errors.raise_error uu____16227
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____16242 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____16242
                          (fun uu____16299  ->
                             match uu____16299 with
                             | (xs1,c1) ->
                                 let uu____16350 =
                                   let uu____16393 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____16393)
                                    in
                                 FStar_Pervasives_Native.Some uu____16350))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____16530 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____16550 = project orig env wl1 i st  in
                      match uu____16550 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____16564) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____16579 = imitate orig env wl1 st  in
                   match uu____16579 with
                   | Failed uu____16584 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____16623 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____16623 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____16646 = forced_lhs_pattern  in
                     (match uu____16646 with
                      | (lhs_t,uu____16648,uu____16649,uu____16650) ->
                          ((let uu____16652 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16652
                            then
                              let uu____16653 = lhs1  in
                              match uu____16653 with
                              | (t0,uu____16655,uu____16656,uu____16657) ->
                                  let uu____16658 = forced_lhs_pattern  in
                                  (match uu____16658 with
                                   | (t11,uu____16660,uu____16661,uu____16662)
                                       ->
                                       let uu____16663 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____16664 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____16663 uu____16664)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____16672 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____16672
                            then
                              ((let uu____16674 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16674
                                then
                                  let uu____16675 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____16676 = names_to_string rhs_vars
                                     in
                                  let uu____16677 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____16675 uu____16676 uu____16677
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____16681 =
                                  let uu____16682 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____16682 wl2  in
                                match uu____16681 with
                                | Failed uu____16683 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____16692 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16692
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____16709 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____16709 with
                 | (hd1,uu____16725) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____16746 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____16759 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____16760 -> true
                      | uu____16777 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____16781 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____16781
                          then true
                          else
                            ((let uu____16784 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____16784
                              then
                                let uu____16785 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____16785
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
                    let uu____16805 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____16805 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____16818 =
                             let uu____16819 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____16819
                              in
                           giveup_or_defer1 orig uu____16818
                         else
                           (let uu____16821 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____16821
                            then
                              let uu____16822 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____16822
                               then
                                 let uu____16823 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____16823
                               else
                                 ((let uu____16828 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____16828
                                   then
                                     let uu____16829 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____16830 = names_to_string fvs1
                                        in
                                     let uu____16831 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____16829 uu____16830 uu____16831
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
                                (let uu____16835 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____16835
                                 then
                                   ((let uu____16837 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____16837
                                     then
                                       let uu____16838 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____16839 = names_to_string fvs1
                                          in
                                       let uu____16840 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____16838 uu____16839 uu____16840
                                     else ());
                                    (let uu____16842 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____16842))
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
                      (let uu____16853 =
                         let uu____16854 = FStar_Syntax_Free.names t1  in
                         check_head uu____16854 t2  in
                       if uu____16853
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____16865 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16865
                           then
                             let uu____16866 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____16867 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____16866 uu____16867
                           else ());
                          (let uu____16875 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____16875))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____16966 uu____16967 r =
                match (uu____16966, uu____16967) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____17165 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____17165
                    then
                      let uu____17166 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____17166
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____17190 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____17190
                        then
                          let uu____17191 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____17192 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____17193 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____17194 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____17195 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____17191 uu____17192 uu____17193 uu____17194
                            uu____17195
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____17261 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____17261 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____17275 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____17275 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____17329 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____17329
                                      in
                                   let uu____17332 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____17332 k3)
                            else
                              (let uu____17336 =
                                 let uu____17337 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____17338 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____17339 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____17337 uu____17338 uu____17339
                                  in
                               failwith uu____17336)
                           in
                        let uu____17340 =
                          let uu____17347 =
                            let uu____17360 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____17360  in
                          match uu____17347 with
                          | (bs,k1') ->
                              let uu____17385 =
                                let uu____17398 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____17398
                                 in
                              (match uu____17385 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____17426 =
                                       let uu____17431 = p_scope orig  in
                                       mk_problem uu____17431 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_40  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_40) uu____17426
                                      in
                                   let uu____17436 =
                                     let uu____17441 =
                                       let uu____17442 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____17442.FStar_Syntax_Syntax.n  in
                                     let uu____17445 =
                                       let uu____17446 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____17446.FStar_Syntax_Syntax.n  in
                                     (uu____17441, uu____17445)  in
                                   (match uu____17436 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____17455,uu____17456) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____17459,FStar_Syntax_Syntax.Tm_type
                                       uu____17460) -> (k2'_ys, [sub_prob])
                                    | uu____17463 ->
                                        let uu____17468 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____17468 with
                                         | (t,uu____17480) ->
                                             let uu____17481 =
                                               new_uvar r zs t  in
                                             (match uu____17481 with
                                              | (k_zs,uu____17493) ->
                                                  let kprob =
                                                    let uu____17495 =
                                                      let uu____17500 =
                                                        p_scope orig  in
                                                      mk_problem uu____17500
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_41  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_41) uu____17495
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____17340 with
                        | (k_u',sub_probs) ->
                            let uu____17513 =
                              let uu____17524 =
                                let uu____17525 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____17525
                                 in
                              let uu____17534 =
                                let uu____17537 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____17537  in
                              let uu____17540 =
                                let uu____17543 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____17543  in
                              (uu____17524, uu____17534, uu____17540)  in
                            (match uu____17513 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____17562 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____17562 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____17581 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____17581
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
                                            let uu____17585 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____17585 with
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
              let solve_one_pat uu____17642 uu____17643 =
                match (uu____17642, uu____17643) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____17761 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____17761
                      then
                        let uu____17762 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____17763 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____17762 uu____17763
                      else ());
                     (let uu____17765 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____17765
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____17784  ->
                               fun uu____17785  ->
                                 match (uu____17784, uu____17785) with
                                 | ((a,uu____17803),(t21,uu____17805)) ->
                                     let uu____17814 =
                                       let uu____17819 = p_scope orig  in
                                       let uu____17820 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____17819 orig
                                         uu____17820
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____17814
                                       (fun _0_42  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_42)) xs args2
                           in
                        let guard =
                          let uu____17826 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____17826  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____17841 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____17841 with
                         | (occurs_ok,uu____17849) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____17857 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____17857
                             then
                               let sol =
                                 let uu____17859 =
                                   let uu____17868 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____17868)  in
                                 TERM uu____17859  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____17875 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____17875
                                then
                                  let uu____17876 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____17876 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____17900,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____17926 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____17926
                                        then
                                          let uu____17927 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____17927
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____17934 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____17936 = lhs  in
              match uu____17936 with
              | (t1,u1,k1,args1) ->
                  let uu____17941 = rhs  in
                  (match uu____17941 with
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
                        | uu____17981 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____17991 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____17991 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____18009) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____18016 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____18016
                                     then
                                       let uu____18017 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____18017
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____18024 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18027 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18027
          then
            let uu____18028 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18028
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____18032 = FStar_Util.physical_equality t1 t2  in
             if uu____18032
             then
               let uu____18033 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____18033
             else
               ((let uu____18036 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____18036
                 then
                   let uu____18037 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____18038 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18039 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____18037
                     uu____18038 uu____18039
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____18042,uu____18043)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____18068,FStar_Syntax_Syntax.Tm_delayed uu____18069)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____18094,uu____18095)
                     ->
                     let uu____18122 =
                       let uu___150_18123 = problem  in
                       let uu____18124 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_18123.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18124;
                         FStar_TypeChecker_Common.relation =
                           (uu___150_18123.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___150_18123.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___150_18123.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_18123.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_18123.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_18123.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_18123.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_18123.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18122 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____18125,uu____18126) ->
                     let uu____18133 =
                       let uu___151_18134 = problem  in
                       let uu____18135 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_18134.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18135;
                         FStar_TypeChecker_Common.relation =
                           (uu___151_18134.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___151_18134.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___151_18134.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_18134.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_18134.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_18134.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_18134.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_18134.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18133 wl
                 | (uu____18136,FStar_Syntax_Syntax.Tm_ascribed uu____18137)
                     ->
                     let uu____18164 =
                       let uu___152_18165 = problem  in
                       let uu____18166 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_18165.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___152_18165.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___152_18165.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18166;
                         FStar_TypeChecker_Common.element =
                           (uu___152_18165.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_18165.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___152_18165.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_18165.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_18165.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_18165.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18164 wl
                 | (uu____18167,FStar_Syntax_Syntax.Tm_meta uu____18168) ->
                     let uu____18175 =
                       let uu___153_18176 = problem  in
                       let uu____18177 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___153_18176.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___153_18176.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___153_18176.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18177;
                         FStar_TypeChecker_Common.element =
                           (uu___153_18176.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___153_18176.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___153_18176.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___153_18176.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___153_18176.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___153_18176.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18175 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____18179),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____18181)) ->
                     let uu____18190 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____18190
                 | (FStar_Syntax_Syntax.Tm_bvar uu____18191,uu____18192) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____18193,FStar_Syntax_Syntax.Tm_bvar uu____18194) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___114_18253 =
                       match uu___114_18253 with
                       | [] -> c
                       | bs ->
                           let uu____18275 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____18275
                        in
                     let uu____18284 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____18284 with
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
                                     let uu____18428 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____18428
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____18430 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_43  ->
                                        FStar_TypeChecker_Common.CProb _0_43)
                                     uu____18430))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___115_18512 =
                       match uu___115_18512 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18546 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____18546 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____18684 =
                                     let uu____18689 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____18690 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____18689
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____18690
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_44  ->
                                        FStar_TypeChecker_Common.TProb _0_44)
                                     uu____18684))
                 | (FStar_Syntax_Syntax.Tm_abs uu____18695,uu____18696) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18723 -> true
                       | uu____18740 -> false  in
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
                         (let uu____18791 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_18799 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_18799.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_18799.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_18799.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_18799.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_18799.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_18799.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_18799.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_18799.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_18799.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_18799.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_18799.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_18799.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_18799.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_18799.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_18799.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_18799.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_18799.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_18799.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_18799.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_18799.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_18799.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_18799.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_18799.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_18799.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_18799.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_18799.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_18799.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_18799.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_18799.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_18799.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_18799.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_18799.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_18799.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_18799.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18791 with
                          | (uu____18802,ty,uu____18804) ->
                              let uu____18805 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18805)
                        in
                     let uu____18806 =
                       let uu____18823 = maybe_eta t1  in
                       let uu____18830 = maybe_eta t2  in
                       (uu____18823, uu____18830)  in
                     (match uu____18806 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_18872 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18872.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_18872.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18872.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18872.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18872.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18872.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18872.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18872.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18895 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18895
                          then
                            let uu____18896 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18896 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18911 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18911.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18911.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18911.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18911.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18911.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18911.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18911.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18911.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18935 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18935
                          then
                            let uu____18936 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18936 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18951 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18951.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18951.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18951.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18951.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18951.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18951.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18951.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18951.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18955 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____18972,FStar_Syntax_Syntax.Tm_abs uu____18973) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____19000 -> true
                       | uu____19017 -> false  in
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
                         (let uu____19068 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_19076 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_19076.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_19076.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_19076.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_19076.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_19076.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_19076.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_19076.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_19076.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_19076.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_19076.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_19076.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_19076.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_19076.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_19076.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_19076.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_19076.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_19076.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_19076.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_19076.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_19076.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_19076.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_19076.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_19076.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_19076.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_19076.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_19076.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_19076.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_19076.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_19076.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_19076.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_19076.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_19076.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_19076.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_19076.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____19068 with
                          | (uu____19079,ty,uu____19081) ->
                              let uu____19082 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19082)
                        in
                     let uu____19083 =
                       let uu____19100 = maybe_eta t1  in
                       let uu____19107 = maybe_eta t2  in
                       (uu____19100, uu____19107)  in
                     (match uu____19083 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_19149 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_19149.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_19149.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_19149.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_19149.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_19149.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_19149.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_19149.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_19149.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19172 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19172
                          then
                            let uu____19173 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19173 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19188 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19188.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19188.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19188.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19188.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19188.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19188.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19188.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19188.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19212 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19212
                          then
                            let uu____19213 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19213 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19228 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19228.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19228.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19228.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19228.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19228.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19228.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19228.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19228.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19232 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____19264 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____19264) &&
                          (let uu____19276 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____19276))
                         &&
                         (let uu____19291 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____19291 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___116_19303 =
                                match uu___116_19303 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____19304 -> true
                                | uu____19305 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____19306 -> false)
                        in
                     let uu____19307 = as_refinement should_delta env wl t1
                        in
                     (match uu____19307 with
                      | (x11,phi1) ->
                          let uu____19314 =
                            as_refinement should_delta env wl t2  in
                          (match uu____19314 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____19322 =
                                   let uu____19327 = p_scope orig  in
                                   mk_problem uu____19327 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_45  ->
                                      FStar_TypeChecker_Common.TProb _0_45)
                                   uu____19322
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
                                 let uu____19367 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____19367
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____19373 =
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
                                   let uu____19379 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19379 impl
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
                                   let uu____19388 =
                                     let uu____19393 =
                                       let uu____19394 = p_scope orig  in
                                       let uu____19401 =
                                         let uu____19408 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____19408]  in
                                       FStar_List.append uu____19394
                                         uu____19401
                                        in
                                     mk_problem uu____19393 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_46  ->
                                        FStar_TypeChecker_Common.TProb _0_46)
                                     uu____19388
                                    in
                                 let uu____19417 =
                                   solve env1
                                     (let uu___157_19419 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___157_19419.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___157_19419.smt_ok);
                                        tcenv = (uu___157_19419.tcenv)
                                      })
                                    in
                                 (match uu____19417 with
                                  | Failed uu____19426 -> fallback ()
                                  | Success uu____19431 ->
                                      let guard =
                                        let uu____19435 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____19440 =
                                          let uu____19441 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____19441
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____19435
                                          uu____19440
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___158_19450 = wl1  in
                                        {
                                          attempting =
                                            (uu___158_19450.attempting);
                                          wl_deferred =
                                            (uu___158_19450.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___158_19450.defer_ok);
                                          smt_ok = (uu___158_19450.smt_ok);
                                          tcenv = (uu___158_19450.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19452,FStar_Syntax_Syntax.Tm_uvar uu____19453) ->
                     let uu____19486 = destruct_flex_t t1  in
                     let uu____19487 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19486 uu____19487
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19488;
                       FStar_Syntax_Syntax.pos = uu____19489;
                       FStar_Syntax_Syntax.vars = uu____19490;_},uu____19491),FStar_Syntax_Syntax.Tm_uvar
                    uu____19492) ->
                     let uu____19545 = destruct_flex_t t1  in
                     let uu____19546 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19545 uu____19546
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19547,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19548;
                       FStar_Syntax_Syntax.pos = uu____19549;
                       FStar_Syntax_Syntax.vars = uu____19550;_},uu____19551))
                     ->
                     let uu____19604 = destruct_flex_t t1  in
                     let uu____19605 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19604 uu____19605
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19606;
                       FStar_Syntax_Syntax.pos = uu____19607;
                       FStar_Syntax_Syntax.vars = uu____19608;_},uu____19609),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19610;
                       FStar_Syntax_Syntax.pos = uu____19611;
                       FStar_Syntax_Syntax.vars = uu____19612;_},uu____19613))
                     ->
                     let uu____19686 = destruct_flex_t t1  in
                     let uu____19687 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19686 uu____19687
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19688,uu____19689) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19706 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19706 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19713;
                       FStar_Syntax_Syntax.pos = uu____19714;
                       FStar_Syntax_Syntax.vars = uu____19715;_},uu____19716),uu____19717)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19754 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19754 t2 wl
                 | (uu____19761,FStar_Syntax_Syntax.Tm_uvar uu____19762) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____19779,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19780;
                       FStar_Syntax_Syntax.pos = uu____19781;
                       FStar_Syntax_Syntax.vars = uu____19782;_},uu____19783))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19820,FStar_Syntax_Syntax.Tm_type uu____19821) ->
                     solve_t' env
                       (let uu___159_19839 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19839.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19839.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19839.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19839.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19839.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19839.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19839.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19839.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19839.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19840;
                       FStar_Syntax_Syntax.pos = uu____19841;
                       FStar_Syntax_Syntax.vars = uu____19842;_},uu____19843),FStar_Syntax_Syntax.Tm_type
                    uu____19844) ->
                     solve_t' env
                       (let uu___159_19882 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19882.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19882.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19882.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19882.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19882.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19882.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19882.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19882.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19882.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19883,FStar_Syntax_Syntax.Tm_arrow uu____19884) ->
                     solve_t' env
                       (let uu___159_19914 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19914.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19914.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19914.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19914.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19914.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19914.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19914.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19914.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19914.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19915;
                       FStar_Syntax_Syntax.pos = uu____19916;
                       FStar_Syntax_Syntax.vars = uu____19917;_},uu____19918),FStar_Syntax_Syntax.Tm_arrow
                    uu____19919) ->
                     solve_t' env
                       (let uu___159_19969 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19969.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19969.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19969.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19969.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19969.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19969.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19969.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19969.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19969.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19970,uu____19971) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19990 =
                          let uu____19991 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19991
                           in
                        if uu____19990
                        then
                          let uu____19992 =
                            FStar_All.pipe_left
                              (fun _0_47  ->
                                 FStar_TypeChecker_Common.TProb _0_47)
                              (let uu___160_19998 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_19998.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_19998.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_19998.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_19998.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_19998.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_19998.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_19998.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_19998.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_19998.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19999 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19992 uu____19999 t2
                            wl
                        else
                          (let uu____20007 = base_and_refinement env t2  in
                           match uu____20007 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20036 =
                                      FStar_All.pipe_left
                                        (fun _0_48  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_48)
                                        (let uu___161_20042 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_20042.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_20042.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_20042.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_20042.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_20042.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_20042.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_20042.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_20042.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_20042.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20043 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20036
                                      uu____20043 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_20057 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_20057.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_20057.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20060 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_49  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_49) uu____20060
                                       in
                                    let guard =
                                      let uu____20072 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20072
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
                         uu____20080;
                       FStar_Syntax_Syntax.pos = uu____20081;
                       FStar_Syntax_Syntax.vars = uu____20082;_},uu____20083),uu____20084)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20123 =
                          let uu____20124 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20124
                           in
                        if uu____20123
                        then
                          let uu____20125 =
                            FStar_All.pipe_left
                              (fun _0_50  ->
                                 FStar_TypeChecker_Common.TProb _0_50)
                              (let uu___160_20131 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_20131.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_20131.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_20131.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_20131.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_20131.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_20131.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_20131.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_20131.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_20131.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20132 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20125 uu____20132 t2
                            wl
                        else
                          (let uu____20140 = base_and_refinement env t2  in
                           match uu____20140 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20169 =
                                      FStar_All.pipe_left
                                        (fun _0_51  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_51)
                                        (let uu___161_20175 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_20175.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_20175.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_20175.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_20175.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_20175.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_20175.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_20175.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_20175.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_20175.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20176 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20169
                                      uu____20176 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_20190 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_20190.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_20190.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20193 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_52  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_52) uu____20193
                                       in
                                    let guard =
                                      let uu____20205 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20205
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____20213,FStar_Syntax_Syntax.Tm_uvar uu____20214) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20232 = base_and_refinement env t1  in
                        match uu____20232 with
                        | (t_base,uu____20244) ->
                            solve_t env
                              (let uu___163_20258 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20258.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20258.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20258.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20258.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20258.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20258.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20258.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20258.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____20259,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20260;
                       FStar_Syntax_Syntax.pos = uu____20261;
                       FStar_Syntax_Syntax.vars = uu____20262;_},uu____20263))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20301 = base_and_refinement env t1  in
                        match uu____20301 with
                        | (t_base,uu____20313) ->
                            solve_t env
                              (let uu___163_20327 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20327.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20327.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20327.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20327.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20327.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20327.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20327.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20327.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____20328,uu____20329) ->
                     let t21 =
                       let uu____20339 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____20339  in
                     solve_t env
                       (let uu___164_20363 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___164_20363.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___164_20363.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___164_20363.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___164_20363.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___164_20363.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___164_20363.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___164_20363.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___164_20363.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___164_20363.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____20364,FStar_Syntax_Syntax.Tm_refine uu____20365) ->
                     let t11 =
                       let uu____20375 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____20375  in
                     solve_t env
                       (let uu___165_20399 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_20399.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_20399.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_20399.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_20399.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_20399.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_20399.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_20399.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_20399.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_20399.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                     let sc_prob =
                       let uu____20479 =
                         let uu____20484 = p_scope orig  in
                         mk_problem uu____20484 orig t11
                           FStar_TypeChecker_Common.EQ t21
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_TypeChecker_Common.TProb _0_53)
                         uu____20479
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____20674 = br1  in
                           (match uu____20674 with
                            | (p1,w1,uu____20693) ->
                                let uu____20706 = br2  in
                                (match uu____20706 with
                                 | (p2,w2,uu____20721) ->
                                     let uu____20726 =
                                       let uu____20727 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____20727  in
                                     if uu____20726
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____20735 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____20735 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____20778 = br2  in
                                            (match uu____20778 with
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
                                                   let uu____20809 =
                                                     p_scope orig  in
                                                   let uu____20816 =
                                                     let uu____20823 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____20823
                                                      in
                                                   FStar_List.append
                                                     uu____20809 uu____20816
                                                    in
                                                 let uu____20834 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____20849,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____20862) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____20895 =
                                                         let uu____20898 =
                                                           let uu____20899 =
                                                             mk_problem scope
                                                               orig w12
                                                               FStar_TypeChecker_Common.EQ
                                                               w23
                                                               FStar_Pervasives_Native.None
                                                               "when clause"
                                                              in
                                                           FStar_All.pipe_left
                                                             (fun _0_54  ->
                                                                FStar_TypeChecker_Common.TProb
                                                                  _0_54)
                                                             uu____20899
                                                            in
                                                         [uu____20898]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20895
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____20834
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____20923 =
                                                          mk_problem scope
                                                            orig e1
                                                            FStar_TypeChecker_Common.EQ
                                                            e21
                                                            FStar_Pervasives_Native.None
                                                            "branch body"
                                                           in
                                                        FStar_All.pipe_left
                                                          (fun _0_55  ->
                                                             FStar_TypeChecker_Common.TProb
                                                               _0_55)
                                                          uu____20923
                                                         in
                                                      let uu____20934 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____20934
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____20995 -> FStar_Pervasives_Native.None  in
                     let uu____21026 = solve_branches brs1 brs2  in
                     (match uu____21026 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let wl1 =
                            solve_prob orig FStar_Pervasives_Native.None []
                              wl
                             in
                          solve env (attempt sub_probs1 wl1))
                 | (FStar_Syntax_Syntax.Tm_match uu____21042,uu____21043) ->
                     let head1 =
                       let uu____21069 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21069
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21113 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21113
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21155 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21155
                       then
                         let uu____21156 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21157 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21158 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21156 uu____21157 uu____21158
                       else ());
                      (let uu____21160 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21160
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21175 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21175
                          then
                            let guard =
                              let uu____21187 =
                                let uu____21188 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21188 = FStar_Syntax_Util.Equal  in
                              if uu____21187
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21192 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   uu____21192)
                               in
                            let uu____21195 = solve_prob orig guard [] wl  in
                            solve env uu____21195
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____21198,uu____21199) ->
                     let head1 =
                       let uu____21209 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21209
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21253 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21253
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21295 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21295
                       then
                         let uu____21296 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21297 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21298 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21296 uu____21297 uu____21298
                       else ());
                      (let uu____21300 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21300
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21315 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21315
                          then
                            let guard =
                              let uu____21327 =
                                let uu____21328 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21328 = FStar_Syntax_Util.Equal  in
                              if uu____21327
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21332 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   uu____21332)
                               in
                            let uu____21335 = solve_prob orig guard [] wl  in
                            solve env uu____21335
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____21338,uu____21339) ->
                     let head1 =
                       let uu____21343 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21343
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21387 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21387
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21429 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21429
                       then
                         let uu____21430 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21431 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21432 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21430 uu____21431 uu____21432
                       else ());
                      (let uu____21434 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21434
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21449 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21449
                          then
                            let guard =
                              let uu____21461 =
                                let uu____21462 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21462 = FStar_Syntax_Util.Equal  in
                              if uu____21461
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21466 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_Pervasives_Native.Some _0_58)
                                   uu____21466)
                               in
                            let uu____21469 = solve_prob orig guard [] wl  in
                            solve env uu____21469
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____21472,uu____21473)
                     ->
                     let head1 =
                       let uu____21477 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21477
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21521 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21521
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21563 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21563
                       then
                         let uu____21564 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21565 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21566 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21564 uu____21565 uu____21566
                       else ());
                      (let uu____21568 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21568
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21583 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21583
                          then
                            let guard =
                              let uu____21595 =
                                let uu____21596 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21596 = FStar_Syntax_Util.Equal  in
                              if uu____21595
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21600 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_Pervasives_Native.Some _0_59)
                                   uu____21600)
                               in
                            let uu____21603 = solve_prob orig guard [] wl  in
                            solve env uu____21603
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____21606,uu____21607) ->
                     let head1 =
                       let uu____21611 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21611
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21655 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21655
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21697 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21697
                       then
                         let uu____21698 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21699 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21700 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21698 uu____21699 uu____21700
                       else ());
                      (let uu____21702 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21702
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21717 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21717
                          then
                            let guard =
                              let uu____21729 =
                                let uu____21730 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21730 = FStar_Syntax_Util.Equal  in
                              if uu____21729
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21734 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____21734)
                               in
                            let uu____21737 = solve_prob orig guard [] wl  in
                            solve env uu____21737
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____21740,uu____21741) ->
                     let head1 =
                       let uu____21759 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21759
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21803 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21803
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21845 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21845
                       then
                         let uu____21846 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21847 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21848 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21846 uu____21847 uu____21848
                       else ());
                      (let uu____21850 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21850
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21865 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21865
                          then
                            let guard =
                              let uu____21877 =
                                let uu____21878 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21878 = FStar_Syntax_Util.Equal  in
                              if uu____21877
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21882 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____21882)
                               in
                            let uu____21885 = solve_prob orig guard [] wl  in
                            solve env uu____21885
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21888,FStar_Syntax_Syntax.Tm_match uu____21889) ->
                     let head1 =
                       let uu____21915 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21915
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21959 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21959
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22001 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22001
                       then
                         let uu____22002 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22003 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22004 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22002 uu____22003 uu____22004
                       else ());
                      (let uu____22006 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22006
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22021 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22021
                          then
                            let guard =
                              let uu____22033 =
                                let uu____22034 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22034 = FStar_Syntax_Util.Equal  in
                              if uu____22033
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22038 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____22038)
                               in
                            let uu____22041 = solve_prob orig guard [] wl  in
                            solve env uu____22041
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22044,FStar_Syntax_Syntax.Tm_uinst uu____22045) ->
                     let head1 =
                       let uu____22055 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22055
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22099 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22099
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22141 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22141
                       then
                         let uu____22142 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22143 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22144 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22142 uu____22143 uu____22144
                       else ());
                      (let uu____22146 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22146
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22161 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22161
                          then
                            let guard =
                              let uu____22173 =
                                let uu____22174 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22174 = FStar_Syntax_Util.Equal  in
                              if uu____22173
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22178 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   uu____22178)
                               in
                            let uu____22181 = solve_prob orig guard [] wl  in
                            solve env uu____22181
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22184,FStar_Syntax_Syntax.Tm_name uu____22185) ->
                     let head1 =
                       let uu____22189 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22189
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22233 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22233
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22275 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22275
                       then
                         let uu____22276 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22277 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22278 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22276 uu____22277 uu____22278
                       else ());
                      (let uu____22280 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22280
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22295 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22295
                          then
                            let guard =
                              let uu____22307 =
                                let uu____22308 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22308 = FStar_Syntax_Util.Equal  in
                              if uu____22307
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22312 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   uu____22312)
                               in
                            let uu____22315 = solve_prob orig guard [] wl  in
                            solve env uu____22315
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22318,FStar_Syntax_Syntax.Tm_constant uu____22319)
                     ->
                     let head1 =
                       let uu____22323 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22323
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22367 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22367
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22409 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22409
                       then
                         let uu____22410 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22411 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22412 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22410 uu____22411 uu____22412
                       else ());
                      (let uu____22414 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22414
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22429 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22429
                          then
                            let guard =
                              let uu____22441 =
                                let uu____22442 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22442 = FStar_Syntax_Util.Equal  in
                              if uu____22441
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22446 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   uu____22446)
                               in
                            let uu____22449 = solve_prob orig guard [] wl  in
                            solve env uu____22449
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22452,FStar_Syntax_Syntax.Tm_fvar uu____22453) ->
                     let head1 =
                       let uu____22457 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22457
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22501 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22501
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22543 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22543
                       then
                         let uu____22544 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22545 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22546 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22544 uu____22545 uu____22546
                       else ());
                      (let uu____22548 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22548
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22563 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22563
                          then
                            let guard =
                              let uu____22575 =
                                let uu____22576 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22576 = FStar_Syntax_Util.Equal  in
                              if uu____22575
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22580 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   uu____22580)
                               in
                            let uu____22583 = solve_prob orig guard [] wl  in
                            solve env uu____22583
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22586,FStar_Syntax_Syntax.Tm_app uu____22587) ->
                     let head1 =
                       let uu____22605 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22605
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22649 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22649
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22691 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22691
                       then
                         let uu____22692 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22693 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22694 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22692 uu____22693 uu____22694
                       else ());
                      (let uu____22696 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22696
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22711 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22711
                          then
                            let guard =
                              let uu____22723 =
                                let uu____22724 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22724 = FStar_Syntax_Util.Equal  in
                              if uu____22723
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22728 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   uu____22728)
                               in
                            let uu____22731 = solve_prob orig guard [] wl  in
                            solve env uu____22731
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____22734,FStar_Syntax_Syntax.Tm_let uu____22735) ->
                     let uu____22760 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____22760
                     then
                       let uu____22761 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____22761
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____22763,uu____22764) ->
                     let uu____22777 =
                       let uu____22782 =
                         let uu____22783 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22784 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22785 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22786 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22783 uu____22784 uu____22785 uu____22786
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22782)
                        in
                     FStar_Errors.raise_error uu____22777
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____22787,FStar_Syntax_Syntax.Tm_let uu____22788) ->
                     let uu____22801 =
                       let uu____22806 =
                         let uu____22807 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22808 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22809 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22810 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22807 uu____22808 uu____22809 uu____22810
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22806)
                        in
                     FStar_Errors.raise_error uu____22801
                       t1.FStar_Syntax_Syntax.pos
                 | uu____22811 -> giveup env "head tag mismatch" orig)))))

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
          let uu____22847 = p_scope orig  in
          mk_problem uu____22847 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____22860 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____22860
           then
             let uu____22861 =
               let uu____22862 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____22862  in
             let uu____22863 =
               let uu____22864 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____22864  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____22861 uu____22863
           else ());
          (let uu____22866 =
             let uu____22867 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____22867  in
           if uu____22866
           then
             let uu____22868 =
               let uu____22869 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____22870 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____22869 uu____22870
                in
             giveup env uu____22868 orig
           else
             (let ret_sub_prob =
                let uu____22873 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                  uu____22873
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____22900  ->
                     fun uu____22901  ->
                       match (uu____22900, uu____22901) with
                       | ((a1,uu____22919),(a2,uu____22921)) ->
                           let uu____22930 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_69  ->
                                FStar_TypeChecker_Common.TProb _0_69)
                             uu____22930)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____22943 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____22943  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22975 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22982)::[] -> wp1
              | uu____22999 ->
                  let uu____23008 =
                    let uu____23009 =
                      let uu____23010 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23010  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23009
                     in
                  failwith uu____23008
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23018 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23018]
              | x -> x  in
            let uu____23020 =
              let uu____23029 =
                let uu____23030 =
                  let uu____23031 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23031 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23030  in
              [uu____23029]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23020;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23032 = lift_c1 ()  in solve_eq uu____23032 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_23038  ->
                       match uu___117_23038 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23039 -> false))
                in
             let uu____23040 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23074)::uu____23075,(wp2,uu____23077)::uu____23078)
                   -> (wp1, wp2)
               | uu____23135 ->
                   let uu____23156 =
                     let uu____23161 =
                       let uu____23162 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23163 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23162 uu____23163
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23161)
                      in
                   FStar_Errors.raise_error uu____23156
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23040 with
             | (wpc1,wpc2) ->
                 let uu____23182 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23182
                 then
                   let uu____23185 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23185 wl
                 else
                   (let uu____23189 =
                      let uu____23196 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23196  in
                    match uu____23189 with
                    | (c2_decl,qualifiers) ->
                        let uu____23217 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23217
                        then
                          let c1_repr =
                            let uu____23221 =
                              let uu____23222 =
                                let uu____23223 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23223  in
                              let uu____23224 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23222 uu____23224
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23221
                             in
                          let c2_repr =
                            let uu____23226 =
                              let uu____23227 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23228 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23227 uu____23228
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23226
                             in
                          let prob =
                            let uu____23230 =
                              let uu____23235 =
                                let uu____23236 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____23237 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23236
                                  uu____23237
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23235
                               in
                            FStar_TypeChecker_Common.TProb uu____23230  in
                          let wl1 =
                            let uu____23239 =
                              let uu____23242 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____23242  in
                            solve_prob orig uu____23239 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23251 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23251
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23254 =
                                     let uu____23261 =
                                       let uu____23262 =
                                         let uu____23277 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23278 =
                                           let uu____23281 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23282 =
                                             let uu____23285 =
                                               let uu____23286 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23286
                                                in
                                             [uu____23285]  in
                                           uu____23281 :: uu____23282  in
                                         (uu____23277, uu____23278)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23262
                                        in
                                     FStar_Syntax_Syntax.mk uu____23261  in
                                   uu____23254 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23295 =
                                    let uu____23302 =
                                      let uu____23303 =
                                        let uu____23318 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23319 =
                                          let uu____23322 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____23323 =
                                            let uu____23326 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____23327 =
                                              let uu____23330 =
                                                let uu____23331 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23331
                                                 in
                                              [uu____23330]  in
                                            uu____23326 :: uu____23327  in
                                          uu____23322 :: uu____23323  in
                                        (uu____23318, uu____23319)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23303
                                       in
                                    FStar_Syntax_Syntax.mk uu____23302  in
                                  uu____23295 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23338 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____23338
                              in
                           let wl1 =
                             let uu____23348 =
                               let uu____23351 =
                                 let uu____23354 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23354 g  in
                               FStar_All.pipe_left
                                 (fun _0_71  ->
                                    FStar_Pervasives_Native.Some _0_71)
                                 uu____23351
                                in
                             solve_prob orig uu____23348 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23367 = FStar_Util.physical_equality c1 c2  in
        if uu____23367
        then
          let uu____23368 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23368
        else
          ((let uu____23371 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23371
            then
              let uu____23372 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____23373 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23372
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23373
            else ());
           (let uu____23375 =
              let uu____23380 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____23381 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____23380, uu____23381)  in
            match uu____23375 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23385),FStar_Syntax_Syntax.Total
                    (t2,uu____23387)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23404 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23404 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23407,FStar_Syntax_Syntax.Total uu____23408) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23426),FStar_Syntax_Syntax.Total
                    (t2,uu____23428)) ->
                     let uu____23445 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23445 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23449),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23451)) ->
                     let uu____23468 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23468 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23472),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23474)) ->
                     let uu____23491 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23491 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23494,FStar_Syntax_Syntax.Comp uu____23495) ->
                     let uu____23504 =
                       let uu___166_23509 = problem  in
                       let uu____23514 =
                         let uu____23515 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23515
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23509.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23514;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23509.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23509.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23509.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23509.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23509.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23509.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23509.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23509.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23504 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23516,FStar_Syntax_Syntax.Comp uu____23517) ->
                     let uu____23526 =
                       let uu___166_23531 = problem  in
                       let uu____23536 =
                         let uu____23537 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23537
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23531.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23536;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23531.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23531.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23531.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23531.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23531.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23531.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23531.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23531.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23526 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23538,FStar_Syntax_Syntax.GTotal uu____23539) ->
                     let uu____23548 =
                       let uu___167_23553 = problem  in
                       let uu____23558 =
                         let uu____23559 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23559
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23553.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23553.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23553.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23558;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23553.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23553.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23553.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23553.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23553.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23553.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23548 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23560,FStar_Syntax_Syntax.Total uu____23561) ->
                     let uu____23570 =
                       let uu___167_23575 = problem  in
                       let uu____23580 =
                         let uu____23581 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23581
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23575.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23575.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23575.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23580;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23575.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23575.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23575.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23575.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23575.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23575.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23570 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23582,FStar_Syntax_Syntax.Comp uu____23583) ->
                     let uu____23584 =
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
                     if uu____23584
                     then
                       let uu____23585 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____23585 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____23591 =
                            let uu____23596 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____23596
                            then (c1_comp, c2_comp)
                            else
                              (let uu____23602 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____23603 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____23602, uu____23603))
                             in
                          match uu____23591 with
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
                           (let uu____23610 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23610
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23612 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____23612 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23615 =
                                  let uu____23616 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____23617 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____23616 uu____23617
                                   in
                                giveup env uu____23615 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23624 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23662  ->
              match uu____23662 with
              | (uu____23675,uu____23676,u,uu____23678,uu____23679,uu____23680)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23624 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____23713 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____23713 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____23731 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23759  ->
                match uu____23759 with
                | (u1,u2) ->
                    let uu____23766 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____23767 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____23766 uu____23767))
         in
      FStar_All.pipe_right uu____23731 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23788,[])) -> "{}"
      | uu____23813 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23830 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____23830
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23833 =
              FStar_List.map
                (fun uu____23843  ->
                   match uu____23843 with
                   | (uu____23848,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23833 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23853 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23853 imps
  
let new_t_problem :
  'Auu____23868 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____23868 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____23868)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____23908 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____23908
                then
                  let uu____23909 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____23910 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23909
                    (rel_to_string rel) uu____23910
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
            let uu____23942 =
              let uu____23945 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_72  -> FStar_Pervasives_Native.Some _0_72)
                uu____23945
               in
            FStar_Syntax_Syntax.new_bv uu____23942 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____23954 =
              let uu____23957 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_73  -> FStar_Pervasives_Native.Some _0_73)
                uu____23957
               in
            let uu____23960 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____23954 uu____23960  in
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
          let uu____23996 = FStar_Options.eager_inference ()  in
          if uu____23996
          then
            let uu___168_23997 = probs  in
            {
              attempting = (uu___168_23997.attempting);
              wl_deferred = (uu___168_23997.wl_deferred);
              ctr = (uu___168_23997.ctr);
              defer_ok = false;
              smt_ok = (uu___168_23997.smt_ok);
              tcenv = (uu___168_23997.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____24008 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____24008
              then
                let uu____24009 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24009
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
          ((let uu____24027 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____24027
            then
              let uu____24028 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24028
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____24032 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____24032
             then
               let uu____24033 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24033
             else ());
            (let f2 =
               let uu____24036 =
                 let uu____24037 = FStar_Syntax_Util.unmeta f1  in
                 uu____24037.FStar_Syntax_Syntax.n  in
               match uu____24036 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24041 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___169_24042 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___169_24042.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_24042.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_24042.FStar_TypeChecker_Env.implicits)
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
            let uu____24067 =
              let uu____24068 =
                let uu____24069 =
                  let uu____24070 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____24070
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24069;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____24068  in
            FStar_All.pipe_left
              (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____24067
  
let with_guard_no_simp :
  'Auu____24101 .
    'Auu____24101 ->
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
            let uu____24124 =
              let uu____24125 =
                let uu____24126 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____24126
                  (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24125;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24124
  
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
          (let uu____24172 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24172
           then
             let uu____24173 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24174 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24173
               uu____24174
           else ());
          (let prob =
             let uu____24177 =
               let uu____24182 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24182
                in
             FStar_All.pipe_left
               (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
               uu____24177
              in
           let g =
             let uu____24190 =
               let uu____24193 = singleton' env prob smt_ok  in
               solve_and_commit env uu____24193
                 (fun uu____24195  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____24190  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24219 = try_teq true env t1 t2  in
        match uu____24219 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____24223 = FStar_TypeChecker_Env.get_range env  in
              let uu____24224 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____24223 uu____24224);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24231 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____24231
              then
                let uu____24232 = FStar_Syntax_Print.term_to_string t1  in
                let uu____24233 = FStar_Syntax_Print.term_to_string t2  in
                let uu____24234 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24232
                  uu____24233 uu____24234
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
          let uu____24256 = FStar_TypeChecker_Env.get_range env  in
          let uu____24257 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____24256 uu____24257
  
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
        (let uu____24282 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24282
         then
           let uu____24283 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____24284 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____24283 uu____24284
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____24288 =
             let uu____24293 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24293 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____24288
            in
         let uu____24298 =
           let uu____24301 = singleton env prob  in
           solve_and_commit env uu____24301
             (fun uu____24303  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____24298)
  
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
      fun uu____24338  ->
        match uu____24338 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24381 =
                 let uu____24386 =
                   let uu____24387 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____24388 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____24387 uu____24388
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____24386)  in
               let uu____24389 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____24381 uu____24389)
               in
            let equiv1 v1 v' =
              let uu____24401 =
                let uu____24406 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24407 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24406, uu____24407)  in
              match uu____24401 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24426 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24456 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24456 with
                      | FStar_Syntax_Syntax.U_unif uu____24463 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24492  ->
                                    match uu____24492 with
                                    | (u,v') ->
                                        let uu____24501 = equiv1 v1 v'  in
                                        if uu____24501
                                        then
                                          let uu____24504 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24504 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24520 -> []))
               in
            let uu____24525 =
              let wl =
                let uu___170_24529 = empty_worklist env  in
                {
                  attempting = (uu___170_24529.attempting);
                  wl_deferred = (uu___170_24529.wl_deferred);
                  ctr = (uu___170_24529.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_24529.smt_ok);
                  tcenv = (uu___170_24529.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24547  ->
                      match uu____24547 with
                      | (lb,v1) ->
                          let uu____24554 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24554 with
                           | USolved wl1 -> ()
                           | uu____24556 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24566 =
              match uu____24566 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24575) -> true
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
                      uu____24598,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24600,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24611) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24618,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24626 -> false)
               in
            let uu____24631 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24646  ->
                      match uu____24646 with
                      | (u,v1) ->
                          let uu____24653 = check_ineq (u, v1)  in
                          if uu____24653
                          then true
                          else
                            ((let uu____24656 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24656
                              then
                                let uu____24657 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24658 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24657
                                  uu____24658
                              else ());
                             false)))
               in
            if uu____24631
            then ()
            else
              ((let uu____24662 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____24662
                then
                  ((let uu____24664 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24664);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24674 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24674))
                else ());
               (let uu____24684 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____24684))
  
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
      let fail1 uu____24742 =
        match uu____24742 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____24756 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____24756
       then
         let uu____24757 = wl_to_string wl  in
         let uu____24758 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____24757 uu____24758
       else ());
      (let g1 =
         let uu____24773 = solve_and_commit env wl fail1  in
         match uu____24773 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___171_24786 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___171_24786.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_24786.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_24786.FStar_TypeChecker_Env.implicits)
             }
         | uu____24791 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___172_24795 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_24795.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_24795.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___172_24795.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____24823 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24823 with
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
            let uu___173_24946 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___173_24946.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___173_24946.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___173_24946.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24947 =
            let uu____24948 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24948  in
          if uu____24947
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____24956 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24957 =
                       let uu____24958 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24958
                        in
                     FStar_Errors.diag uu____24956 uu____24957)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____24962 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____24963 =
                        let uu____24964 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____24964
                         in
                      FStar_Errors.diag uu____24962 uu____24963)
                   else ();
                   (let uu____24967 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____24967 "discharge_guard'"
                      env vc1);
                   (let uu____24968 = check_trivial vc1  in
                    match uu____24968 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____24975 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24976 =
                                let uu____24977 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____24977
                                 in
                              FStar_Errors.diag uu____24975 uu____24976)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____24982 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24983 =
                                let uu____24984 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____24984
                                 in
                              FStar_Errors.diag uu____24982 uu____24983)
                           else ();
                           (let vcs =
                              let uu____24995 = FStar_Options.use_tactics ()
                                 in
                              if uu____24995
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____25015  ->
                                     (let uu____25017 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a239  -> ())
                                        uu____25017);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____25060  ->
                                              match uu____25060 with
                                              | (env1,goal,opts) ->
                                                  let uu____25076 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____25076, opts)))))
                              else
                                (let uu____25078 =
                                   let uu____25085 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____25085)  in
                                 [uu____25078])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25118  ->
                                    match uu____25118 with
                                    | (env1,goal,opts) ->
                                        let uu____25128 = check_trivial goal
                                           in
                                        (match uu____25128 with
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
                                                (let uu____25136 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25137 =
                                                   let uu____25138 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25139 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25138 uu____25139
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25136 uu____25137)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25142 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25143 =
                                                   let uu____25144 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25144
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25142 uu____25143)
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
      let uu____25158 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25158 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____25165 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____25165
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25176 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____25176 with
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
          let uu____25204 = FStar_Syntax_Unionfind.find u  in
          match uu____25204 with
          | FStar_Pervasives_Native.None  -> true
          | uu____25207 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____25229 = acc  in
          match uu____25229 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____25315 = hd1  in
                   (match uu____25315 with
                    | (uu____25328,env,u,tm,k,r) ->
                        let uu____25334 = unresolved u  in
                        if uu____25334
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___174_25364 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___174_25364.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___174_25364.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___174_25364.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___174_25364.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___174_25364.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___174_25364.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___174_25364.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___174_25364.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___174_25364.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___174_25364.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___174_25364.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___174_25364.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___174_25364.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___174_25364.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___174_25364.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___174_25364.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___174_25364.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___174_25364.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___174_25364.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___174_25364.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___174_25364.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___174_25364.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___174_25364.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___174_25364.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___174_25364.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___174_25364.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___174_25364.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___174_25364.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___174_25364.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___174_25364.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___174_25364.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___174_25364.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___174_25364.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___174_25364.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___174_25364.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___174_25364.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____25367 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____25367
                            then
                              let uu____25368 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____25369 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____25370 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____25368 uu____25369 uu____25370
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____25381 =
                                      let uu____25390 =
                                        let uu____25397 =
                                          let uu____25398 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____25399 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____25398 uu____25399
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____25397, r)
                                         in
                                      [uu____25390]  in
                                    FStar_Errors.add_errors uu____25381);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___177_25413 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___177_25413.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___177_25413.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___177_25413.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____25416 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25423  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____25416 with
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
        let uu___178_25451 = g  in
        let uu____25452 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___178_25451.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___178_25451.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___178_25451.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25452
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
        let uu____25514 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25514 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25527 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a240  -> ()) uu____25527
      | (reason,uu____25529,uu____25530,e,t,r)::uu____25534 ->
          let uu____25561 =
            let uu____25566 =
              let uu____25567 = FStar_Syntax_Print.term_to_string t  in
              let uu____25568 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25567 uu____25568
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25566)
             in
          FStar_Errors.raise_error uu____25561 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___179_25579 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_25579.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_25579.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_25579.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25606 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25606 with
      | FStar_Pervasives_Native.Some uu____25612 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25628 = try_teq false env t1 t2  in
        match uu____25628 with
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
        (let uu____25654 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25654
         then
           let uu____25655 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25656 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25655
             uu____25656
         else ());
        (let uu____25658 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25658 with
         | (prob,x) ->
             let g =
               let uu____25674 =
                 let uu____25677 = singleton' env prob true  in
                 solve_and_commit env uu____25677
                   (fun uu____25679  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25674  in
             ((let uu____25689 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____25689
               then
                 let uu____25690 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____25691 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____25692 =
                   let uu____25693 = FStar_Util.must g  in
                   guard_to_string env uu____25693  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____25690 uu____25691 uu____25692
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
        let uu____25727 = check_subtyping env t1 t2  in
        match uu____25727 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25746 =
              let uu____25747 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____25747 g  in
            FStar_Pervasives_Native.Some uu____25746
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25765 = check_subtyping env t1 t2  in
        match uu____25765 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25784 =
              let uu____25785 =
                let uu____25786 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25786]  in
              close_guard env uu____25785 g  in
            FStar_Pervasives_Native.Some uu____25784
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____25803 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25803
         then
           let uu____25804 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25805 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25804
             uu____25805
         else ());
        (let uu____25807 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25807 with
         | (prob,x) ->
             let g =
               let uu____25817 =
                 let uu____25820 = singleton' env prob false  in
                 solve_and_commit env uu____25820
                   (fun uu____25822  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25817  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____25833 =
                      let uu____25834 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____25834]  in
                    close_guard env uu____25833 g1  in
                  discharge_guard_nosmt env g2))
  