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
                 uu____6505),uu____6506)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6524 =
                     let uu____6533 = maybe_inline t11  in
                     let uu____6536 = maybe_inline t21  in
                     (uu____6533, uu____6536)  in
                   match uu____6524 with
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
                (uu____6573,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6574))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6592 =
                     let uu____6601 = maybe_inline t11  in
                     let uu____6604 = maybe_inline t21  in
                     (uu____6601, uu____6604)  in
                   match uu____6592 with
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
            | MisMatch uu____6653 -> fail1 r
            | uu____6662 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6675 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6675
           then
             let uu____6676 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6677 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6678 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6676
               uu____6677 uu____6678
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6724 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6768 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___106_6782  ->
    match uu___106_6782 with
    | T (t,uu____6784) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6808 = FStar_Syntax_Util.type_u ()  in
      match uu____6808 with
      | (t,uu____6814) ->
          let uu____6815 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6815
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6830 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6830 FStar_Pervasives_Native.fst
  
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
        let uu____6904 = head_matches env t1 t'  in
        match uu____6904 with
        | MisMatch uu____6905 -> false
        | uu____6914 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____7014,imp),T (t2,uu____7017)) -> (t2, imp)
                     | uu____7040 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7107  ->
                    match uu____7107 with
                    | (t2,uu____7121) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7168 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7168 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7253))::tcs2) ->
                       aux
                         (((let uu___131_7292 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_7292.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_7292.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7310 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___107_7367 =
                 match uu___107_7367 with
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
               let uu____7486 = decompose1 [] bs1  in
               (rebuild, matches, uu____7486))
      | uu____7537 ->
          let rebuild uu___108_7545 =
            match uu___108_7545 with
            | [] -> t1
            | uu____7548 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___109_7583  ->
    match uu___109_7583 with
    | T (t,uu____7585) -> t
    | uu____7598 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___110_7603  ->
    match uu___110_7603 with
    | T (t,uu____7605) -> FStar_Syntax_Syntax.as_arg t
    | uu____7618 -> failwith "Impossible"
  
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
              | (uu____7750,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7779 = new_uvar r scope1 k  in
                  (match uu____7779 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7797 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7814 =
                         let uu____7815 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_23  ->
                              FStar_TypeChecker_Common.TProb _0_23)
                           uu____7815
                          in
                       ((T (gi_xs, mk_kind)), uu____7814))
              | (uu____7830,uu____7831,C uu____7832) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7985 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8002;
                         FStar_Syntax_Syntax.vars = uu____8003;_})
                        ->
                        let uu____8026 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8026 with
                         | (T (gi_xs,uu____8052),prob) ->
                             let uu____8066 =
                               let uu____8067 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_24  -> C _0_24)
                                 uu____8067
                                in
                             (uu____8066, [prob])
                         | uu____8070 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8085;
                         FStar_Syntax_Syntax.vars = uu____8086;_})
                        ->
                        let uu____8109 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8109 with
                         | (T (gi_xs,uu____8135),prob) ->
                             let uu____8149 =
                               let uu____8150 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_25  -> C _0_25)
                                 uu____8150
                                in
                             (uu____8149, [prob])
                         | uu____8153 -> failwith "impossible")
                    | (uu____8164,uu____8165,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8167;
                         FStar_Syntax_Syntax.vars = uu____8168;_})
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
                        let uu____8303 =
                          let uu____8312 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8312 FStar_List.unzip
                           in
                        (match uu____8303 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8366 =
                                 let uu____8367 =
                                   let uu____8370 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8370 un_T  in
                                 let uu____8371 =
                                   let uu____8380 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8380
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8367;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8371;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8366
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8389 ->
                        let uu____8402 = sub_prob scope1 args q  in
                        (match uu____8402 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7985 with
                   | (tc,probs) ->
                       let uu____8433 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8496,uu____8497),T
                            (t,uu____8499)) ->
                             let b1 =
                               ((let uu___132_8540 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___132_8540.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___132_8540.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8541 =
                               let uu____8548 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8548 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8541)
                         | uu____8583 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8433 with
                        | (bopt,scope2,args1) ->
                            let uu____8667 = aux scope2 args1 qs2  in
                            (match uu____8667 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8705 =
                                           let uu____8708 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8708  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8705
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
                                         let uu____8733 =
                                           let uu____8736 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8737 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8736 :: uu____8737  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8733
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
  'Auu____8811 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8811)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8811)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___133_8834 = p  in
      let uu____8839 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8840 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___133_8834.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8839;
        FStar_TypeChecker_Common.relation =
          (uu___133_8834.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8840;
        FStar_TypeChecker_Common.element =
          (uu___133_8834.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___133_8834.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___133_8834.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___133_8834.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___133_8834.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___133_8834.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8856 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8856
            (fun _0_26  -> FStar_TypeChecker_Common.TProb _0_26)
      | FStar_TypeChecker_Common.CProb uu____8865 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8889 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8889 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8899 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8899 with
           | (lh,uu____8919) ->
               let uu____8940 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8940 with
                | (rh,uu____8960) ->
                    let uu____8981 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8998,FStar_Syntax_Syntax.Tm_uvar uu____8999)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9036,uu____9037)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9058,FStar_Syntax_Syntax.Tm_uvar uu____9059)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9080,uu____9081)
                          ->
                          let uu____9098 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9098 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9147 ->
                                    let rank =
                                      let uu____9155 = is_top_level_prob prob
                                         in
                                      if uu____9155
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9157 =
                                      let uu___134_9162 = tp  in
                                      let uu____9167 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___134_9162.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___134_9162.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___134_9162.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9167;
                                        FStar_TypeChecker_Common.element =
                                          (uu___134_9162.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___134_9162.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___134_9162.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___134_9162.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___134_9162.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___134_9162.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9157)))
                      | (uu____9178,FStar_Syntax_Syntax.Tm_uvar uu____9179)
                          ->
                          let uu____9196 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9196 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9245 ->
                                    let uu____9252 =
                                      let uu___135_9259 = tp  in
                                      let uu____9264 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_9259.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9264;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_9259.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___135_9259.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_9259.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_9259.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_9259.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_9259.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_9259.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_9259.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9252)))
                      | (uu____9281,uu____9282) -> (rigid_rigid, tp)  in
                    (match uu____8981 with
                     | (rank,tp1) ->
                         let uu____9301 =
                           FStar_All.pipe_right
                             (let uu___136_9307 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___136_9307.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___136_9307.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___136_9307.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___136_9307.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___136_9307.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___136_9307.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___136_9307.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___136_9307.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___136_9307.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_27  ->
                                FStar_TypeChecker_Common.TProb _0_27)
                            in
                         (rank, uu____9301))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9317 =
            FStar_All.pipe_right
              (let uu___137_9323 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_9323.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_9323.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_9323.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_9323.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_9323.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_9323.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___137_9323.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_9323.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_9323.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_28  -> FStar_TypeChecker_Common.CProb _0_28)
             in
          (rigid_rigid, uu____9317)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9384 probs =
      match uu____9384 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9437 = rank wl hd1  in
               (match uu____9437 with
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
    match projectee with | UDeferred _0 -> true | uu____9553 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9567 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9581 -> false
  
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
                        let uu____9633 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9633 with
                        | (k,uu____9639) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9649 -> false)))
            | uu____9650 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9702 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9708 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9708 = (Prims.parse_int "0")))
                           in
                        if uu____9702 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9724 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9730 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9730 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9724)
               in
            let uu____9731 = filter1 u12  in
            let uu____9734 = filter1 u22  in (uu____9731, uu____9734)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9763 = filter_out_common_univs us1 us2  in
                (match uu____9763 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9822 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9822 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9825 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9835 =
                          let uu____9836 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9837 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9836
                            uu____9837
                           in
                        UFailed uu____9835))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9861 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9861 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9887 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9887 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9890 ->
                let uu____9895 =
                  let uu____9896 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9897 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9896
                    uu____9897 msg
                   in
                UFailed uu____9895
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9898,uu____9899) ->
              let uu____9900 =
                let uu____9901 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9902 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9901 uu____9902
                 in
              failwith uu____9900
          | (FStar_Syntax_Syntax.U_unknown ,uu____9903) ->
              let uu____9904 =
                let uu____9905 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9906 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9905 uu____9906
                 in
              failwith uu____9904
          | (uu____9907,FStar_Syntax_Syntax.U_bvar uu____9908) ->
              let uu____9909 =
                let uu____9910 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9911 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9910 uu____9911
                 in
              failwith uu____9909
          | (uu____9912,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9913 =
                let uu____9914 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9915 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9914 uu____9915
                 in
              failwith uu____9913
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9939 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9939
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9961 = occurs_univ v1 u3  in
              if uu____9961
              then
                let uu____9962 =
                  let uu____9963 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9964 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9963 uu____9964
                   in
                try_umax_components u11 u21 uu____9962
              else
                (let uu____9966 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9966)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9986 = occurs_univ v1 u3  in
              if uu____9986
              then
                let uu____9987 =
                  let uu____9988 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9989 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9988 uu____9989
                   in
                try_umax_components u11 u21 uu____9987
              else
                (let uu____9991 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9991)
          | (FStar_Syntax_Syntax.U_max uu____10000,uu____10001) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10007 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10007
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10009,FStar_Syntax_Syntax.U_max uu____10010) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10016 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10016
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10018,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10019,FStar_Syntax_Syntax.U_name uu____10020) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10021) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10022) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10023,FStar_Syntax_Syntax.U_succ uu____10024) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10025,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10125 = bc1  in
      match uu____10125 with
      | (bs1,mk_cod1) ->
          let uu____10169 = bc2  in
          (match uu____10169 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10280 = aux xs ys  in
                     (match uu____10280 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10363 =
                       let uu____10370 = mk_cod1 xs  in ([], uu____10370)  in
                     let uu____10373 =
                       let uu____10380 = mk_cod2 ys  in ([], uu____10380)  in
                     (uu____10363, uu____10373)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10565 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10565
       then
         let uu____10566 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10566
       else ());
      (let uu____10568 = next_prob probs  in
       match uu____10568 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___138_10589 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___138_10589.wl_deferred);
               ctr = (uu___138_10589.ctr);
               defer_ok = (uu___138_10589.defer_ok);
               smt_ok = (uu___138_10589.smt_ok);
               tcenv = (uu___138_10589.tcenv)
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
                  let uu____10600 = solve_flex_rigid_join env tp probs1  in
                  (match uu____10600 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10605 = solve_rigid_flex_meet env tp probs1
                        in
                     match uu____10605 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10610,uu____10611) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10628 ->
                let uu____10637 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10696  ->
                          match uu____10696 with
                          | (c,uu____10704,uu____10705) -> c < probs.ctr))
                   in
                (match uu____10637 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10746 =
                            FStar_List.map
                              (fun uu____10761  ->
                                 match uu____10761 with
                                 | (uu____10772,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10746
                      | uu____10775 ->
                          let uu____10784 =
                            let uu___139_10785 = probs  in
                            let uu____10786 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10807  ->
                                      match uu____10807 with
                                      | (uu____10814,uu____10815,y) -> y))
                               in
                            {
                              attempting = uu____10786;
                              wl_deferred = rest;
                              ctr = (uu___139_10785.ctr);
                              defer_ok = (uu___139_10785.defer_ok);
                              smt_ok = (uu___139_10785.smt_ok);
                              tcenv = (uu___139_10785.tcenv)
                            }  in
                          solve env uu____10784))))

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
            let uu____10822 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10822 with
            | USolved wl1 ->
                let uu____10824 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10824
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
                  let uu____10876 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10876 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10879 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10891;
                  FStar_Syntax_Syntax.vars = uu____10892;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10895;
                  FStar_Syntax_Syntax.vars = uu____10896;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10908,uu____10909) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10916,FStar_Syntax_Syntax.Tm_uinst uu____10917) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10924 -> USolved wl

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
            ((let uu____10934 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10934
              then
                let uu____10935 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10935 msg
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
        (let uu____10944 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10944
         then
           let uu____10945 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10945
         else ());
        (let uu____10947 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10947 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____11013 = head_matches_delta env () t1 t2  in
               match uu____11013 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____11054 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____11103 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____11118 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____11119 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____11118, uu____11119)
                          | FStar_Pervasives_Native.None  ->
                              let uu____11124 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____11125 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____11124, uu____11125)
                           in
                        (match uu____11103 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11155 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_29  ->
                                    FStar_TypeChecker_Common.TProb _0_29)
                                 uu____11155
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11186 =
                                    let uu____11195 =
                                      let uu____11198 =
                                        let uu____11205 =
                                          let uu____11206 =
                                            let uu____11213 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____11213)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11206
                                           in
                                        FStar_Syntax_Syntax.mk uu____11205
                                         in
                                      uu____11198
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____11221 =
                                      let uu____11224 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____11224]  in
                                    (uu____11195, uu____11221)  in
                                  FStar_Pervasives_Native.Some uu____11186
                              | (uu____11237,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11239)) ->
                                  let uu____11244 =
                                    let uu____11251 =
                                      let uu____11254 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____11254]  in
                                    (t11, uu____11251)  in
                                  FStar_Pervasives_Native.Some uu____11244
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11264),uu____11265) ->
                                  let uu____11270 =
                                    let uu____11277 =
                                      let uu____11280 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____11280]  in
                                    (t21, uu____11277)  in
                                  FStar_Pervasives_Native.Some uu____11270
                              | uu____11289 ->
                                  let uu____11294 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____11294 with
                                   | (head1,uu____11318) ->
                                       let uu____11339 =
                                         let uu____11340 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____11340.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____11339 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11351;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11353;_}
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
                                        | uu____11360 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11373) ->
                  let uu____11398 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___111_11424  ->
                            match uu___111_11424 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11431 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____11431 with
                                      | (u',uu____11447) ->
                                          let uu____11468 =
                                            let uu____11469 = whnf env u'  in
                                            uu____11469.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11468 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11473) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11498 -> false))
                                 | uu____11499 -> false)
                            | uu____11502 -> false))
                     in
                  (match uu____11398 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11540 tps =
                         match uu____11540 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11588 =
                                    let uu____11597 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____11597  in
                                  (match uu____11588 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11632 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11641 =
                         let uu____11650 =
                           let uu____11657 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11657, [])  in
                         make_lower_bound uu____11650 lower_bounds  in
                       (match uu____11641 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11669 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11669
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
                            ((let uu____11689 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11689
                              then
                                let wl' =
                                  let uu___140_11691 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___140_11691.wl_deferred);
                                    ctr = (uu___140_11691.ctr);
                                    defer_ok = (uu___140_11691.defer_ok);
                                    smt_ok = (uu___140_11691.smt_ok);
                                    tcenv = (uu___140_11691.tcenv)
                                  }  in
                                let uu____11692 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11692
                              else ());
                             (let uu____11694 =
                                solve_t env eq_prob
                                  (let uu___141_11696 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___141_11696.wl_deferred);
                                     ctr = (uu___141_11696.ctr);
                                     defer_ok = (uu___141_11696.defer_ok);
                                     smt_ok = (uu___141_11696.smt_ok);
                                     tcenv = (uu___141_11696.tcenv)
                                   })
                                 in
                              match uu____11694 with
                              | Success uu____11699 ->
                                  let wl1 =
                                    let uu___142_11701 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___142_11701.wl_deferred);
                                      ctr = (uu___142_11701.ctr);
                                      defer_ok = (uu___142_11701.defer_ok);
                                      smt_ok = (uu___142_11701.smt_ok);
                                      tcenv = (uu___142_11701.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11703 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11708 -> FStar_Pervasives_Native.None))))
              | uu____11709 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11718 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11718
         then
           let uu____11719 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11719
         else ());
        (let uu____11721 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11721 with
         | (u,args) ->
             let uu____11760 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11760 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____11809 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____11809 with
                    | (h1,args1) ->
                        let uu____11850 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11850 with
                         | (h2,uu____11870) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11897 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11897
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11915 =
                                          let uu____11918 =
                                            let uu____11919 =
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
                                                   _0_30) uu____11919
                                             in
                                          [uu____11918]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11915))
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
                                       (let uu____11952 =
                                          let uu____11955 =
                                            let uu____11956 =
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
                                                   _0_31) uu____11956
                                             in
                                          [uu____11955]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11952))
                                  else FStar_Pervasives_Native.None
                              | uu____11970 -> FStar_Pervasives_Native.None))
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
                             let uu____12064 =
                               let uu____12073 =
                                 let uu____12076 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____12076  in
                               (uu____12073, m1)  in
                             FStar_Pervasives_Native.Some uu____12064)
                    | (uu____12089,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12091)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12139),uu____12140) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12187 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12240) ->
                       let uu____12265 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___112_12291  ->
                                 match uu___112_12291 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12298 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____12298 with
                                           | (u',uu____12314) ->
                                               let uu____12335 =
                                                 let uu____12336 =
                                                   whnf env u'  in
                                                 uu____12336.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____12335 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12340) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12365 -> false))
                                      | uu____12366 -> false)
                                 | uu____12369 -> false))
                          in
                       (match uu____12265 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12411 tps =
                              match uu____12411 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12473 =
                                         let uu____12484 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____12484  in
                                       (match uu____12473 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12535 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____12546 =
                              let uu____12557 =
                                let uu____12566 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____12566, [])  in
                              make_upper_bound uu____12557 upper_bounds  in
                            (match uu____12546 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12580 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12580
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
                                 ((let uu____12606 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12606
                                   then
                                     let wl' =
                                       let uu___143_12608 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___143_12608.wl_deferred);
                                         ctr = (uu___143_12608.ctr);
                                         defer_ok = (uu___143_12608.defer_ok);
                                         smt_ok = (uu___143_12608.smt_ok);
                                         tcenv = (uu___143_12608.tcenv)
                                       }  in
                                     let uu____12609 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12609
                                   else ());
                                  (let uu____12611 =
                                     solve_t env eq_prob
                                       (let uu___144_12613 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___144_12613.wl_deferred);
                                          ctr = (uu___144_12613.ctr);
                                          defer_ok =
                                            (uu___144_12613.defer_ok);
                                          smt_ok = (uu___144_12613.smt_ok);
                                          tcenv = (uu___144_12613.tcenv)
                                        })
                                      in
                                   match uu____12611 with
                                   | Success uu____12616 ->
                                       let wl1 =
                                         let uu___145_12618 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___145_12618.wl_deferred);
                                           ctr = (uu___145_12618.ctr);
                                           defer_ok =
                                             (uu___145_12618.defer_ok);
                                           smt_ok = (uu___145_12618.smt_ok);
                                           tcenv = (uu___145_12618.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____12620 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12625 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12626 -> failwith "Impossible: Not a flex-rigid")))

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
              (let uu____12644 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12644
               then
                 let uu____12645 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12646 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12645 (rel_to_string (p_rel orig)) uu____12646
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____12716 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____12716
                       then
                         let uu____12717 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____12717
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___146_12771 = hd1  in
                       let uu____12772 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___146_12771.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___146_12771.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12772
                       }  in
                     let hd21 =
                       let uu___147_12776 = hd2  in
                       let uu____12777 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___147_12776.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___147_12776.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12777
                       }  in
                     let prob =
                       let uu____12781 =
                         let uu____12786 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____12786 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
                         uu____12781
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____12797 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____12797
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____12801 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____12801 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____12839 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____12844 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____12839 uu____12844
                             in
                          ((let uu____12854 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12854
                            then
                              let uu____12855 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____12856 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____12855 uu____12856
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____12879 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____12889 = aux scope env [] bs1 bs2  in
               match uu____12889 with
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
        (let uu____12914 = compress_tprob wl problem  in
         solve_t' env uu____12914 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12966 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12966 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12997,uu____12998) ->
                    let rec may_relate head3 =
                      let uu____13025 =
                        let uu____13026 = FStar_Syntax_Subst.compress head3
                           in
                        uu____13026.FStar_Syntax_Syntax.n  in
                      match uu____13025 with
                      | FStar_Syntax_Syntax.Tm_name uu____13029 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____13030 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13053;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____13054;
                            FStar_Syntax_Syntax.fv_qual = uu____13055;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13058;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13059;
                            FStar_Syntax_Syntax.fv_qual = uu____13060;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13064,uu____13065) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13107) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13113) ->
                          may_relate t
                      | uu____13118 -> false  in
                    let uu____13119 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13119
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
                                 let uu____13140 =
                                   let uu____13141 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13141 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13140
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____13143 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____13143
                    else
                      (let uu____13145 =
                         let uu____13146 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13147 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13146 uu____13147
                          in
                       giveup env1 uu____13145 orig)
                | (uu____13148,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___148_13162 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_13162.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_13162.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___148_13162.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_13162.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_13162.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_13162.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_13162.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_13162.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13163,FStar_Pervasives_Native.None ) ->
                    ((let uu____13175 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13175
                      then
                        let uu____13176 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13177 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13178 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13179 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____13176
                          uu____13177 uu____13178 uu____13179
                      else ());
                     (let uu____13181 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13181 with
                      | (head11,args1) ->
                          let uu____13218 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13218 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____13272 =
                                   let uu____13273 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____13274 = args_to_string args1  in
                                   let uu____13275 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____13276 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____13273 uu____13274 uu____13275
                                     uu____13276
                                    in
                                 giveup env1 uu____13272 orig
                               else
                                 (let uu____13278 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____13284 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____13284 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____13278
                                  then
                                    let uu____13285 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____13285 with
                                    | USolved wl2 ->
                                        let uu____13287 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____13287
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____13291 =
                                       base_and_refinement env1 t1  in
                                     match uu____13291 with
                                     | (base1,refinement1) ->
                                         let uu____13316 =
                                           base_and_refinement env1 t2  in
                                         (match uu____13316 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13373 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13373 with
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
                                                            (fun uu____13395 
                                                               ->
                                                               fun
                                                                 uu____13396 
                                                                 ->
                                                                 match 
                                                                   (uu____13395,
                                                                    uu____13396)
                                                                 with
                                                                 | ((a,uu____13414),
                                                                    (a',uu____13416))
                                                                    ->
                                                                    let uu____13425
                                                                    =
                                                                    let uu____13430
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____13430
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
                                                                    uu____13425)
                                                            args1 args2
                                                           in
                                                        let formula =
                                                          let uu____13436 =
                                                            FStar_List.map
                                                              (fun p  ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____13436
                                                           in
                                                        let wl3 =
                                                          solve_prob orig
                                                            (FStar_Pervasives_Native.Some
                                                               formula) []
                                                            wl2
                                                           in
                                                        solve env1
                                                          (attempt subprobs
                                                             wl3))
                                               | uu____13442 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___149_13478 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___149_13478.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____13515 =
           match uu____13515 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____13559 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____13559 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____13671  ->
                      let uu____13672 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____13672);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____13740  ->
                                match uu____13740 with
                                | (x,imp) ->
                                    let uu____13751 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____13751, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____13764 = FStar_Syntax_Util.type_u ()  in
                        match uu____13764 with
                        | (t1,uu____13770) ->
                            let uu____13771 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____13771
                         in
                      let uu____13776 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____13776 with
                       | (t',tm_u1) ->
                           let uu____13789 = destruct_flex_t t'  in
                           (match uu____13789 with
                            | (uu____13826,u1,k1,uu____13829) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____13888 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13888
                                   in
                                let sol =
                                  let uu____13892 =
                                    let uu____13901 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13901)  in
                                  TERM uu____13892  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____14036  ->
                            let uu____14037 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____14038 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____14037 uu____14038);
                       (let uu____14051 = pat_var_opt env pat_args hd1  in
                        match uu____14051 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____14071  ->
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
                                       (fun uu____14114  ->
                                          match uu____14114 with
                                          | (x,uu____14120) ->
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
                                 (fun uu____14135  ->
                                    let uu____14136 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____14149 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____14136
                                      uu____14149);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____14153 =
                                  let uu____14154 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____14154  in
                                if uu____14153
                                then
                                  (debug1
                                     (fun uu____14166  ->
                                        let uu____14167 =
                                          let uu____14170 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____14183 =
                                            let uu____14186 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____14187 =
                                              let uu____14190 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____14191 =
                                                let uu____14194 =
                                                  names_to_string fvs  in
                                                let uu____14195 =
                                                  let uu____14198 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____14198]  in
                                                uu____14194 :: uu____14195
                                                 in
                                              uu____14190 :: uu____14191  in
                                            uu____14186 :: uu____14187  in
                                          uu____14170 :: uu____14183  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____14167);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____14200 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____14203 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____14200 (formal ::
                                     pattern_vars) uu____14203 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____14210::uu____14211) ->
                      let uu____14242 =
                        let uu____14255 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____14255  in
                      (match uu____14242 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____14294 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____14301::uu____14302,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____14325 =
                 let uu____14338 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____14338  in
               (match uu____14325 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____14374  ->
                          let uu____14375 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14376 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14377 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14378 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14375 uu____14376 uu____14377 uu____14378);
                     (let uu____14379 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____14382 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____14379 [] uu____14382 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____14428 = lhs  in
           match uu____14428 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____14438 ->
                     let uu____14439 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____14439 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____14470 = p  in
           match uu____14470 with
           | (((u,k),xs,c),ps,(h,uu____14481,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14569 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____14569 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____14592 = h gs_xs  in
                      let uu____14593 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                         in
                      FStar_Syntax_Util.abs xs1 uu____14592 uu____14593  in
                    ((let uu____14599 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14599
                      then
                        let uu____14600 =
                          let uu____14603 =
                            let uu____14604 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____14604
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____14609 =
                            let uu____14612 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____14613 =
                              let uu____14616 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____14617 =
                                let uu____14620 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____14621 =
                                  let uu____14624 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____14625 =
                                    let uu____14628 =
                                      let uu____14629 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____14629
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____14634 =
                                      let uu____14637 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____14637]  in
                                    uu____14628 :: uu____14634  in
                                  uu____14624 :: uu____14625  in
                                uu____14620 :: uu____14621  in
                              uu____14616 :: uu____14617  in
                            uu____14612 :: uu____14613  in
                          uu____14603 :: uu____14609  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____14600
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___113_14667 =
           match uu___113_14667 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____14709 = p  in
           match uu____14709 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14806 = FStar_List.nth ps i  in
               (match uu____14806 with
                | (pi,uu____14810) ->
                    let uu____14815 = FStar_List.nth xs i  in
                    (match uu____14815 with
                     | (xi,uu____14827) ->
                         let rec gs k =
                           let uu____14842 =
                             let uu____14855 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____14855  in
                           match uu____14842 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____14934)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____14947 = new_uvar r xs k_a  in
                                     (match uu____14947 with
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
                                          let uu____14969 = aux subst2 tl1
                                             in
                                          (match uu____14969 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____14996 =
                                                 let uu____14999 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____14999 :: gi_xs'  in
                                               let uu____15000 =
                                                 let uu____15003 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____15003 :: gi_ps'  in
                                               (uu____14996, uu____15000)))
                                  in
                               aux [] bs
                            in
                         let uu____15008 =
                           let uu____15009 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____15009
                            in
                         if uu____15008
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____15013 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____15013 with
                            | (g_xs,uu____15025) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____15036 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____15037 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_35  ->
                                         FStar_Pervasives_Native.Some _0_35)
                                     in
                                  FStar_Syntax_Util.abs xs uu____15036
                                    uu____15037
                                   in
                                let sub1 =
                                  let uu____15043 =
                                    let uu____15048 = p_scope orig  in
                                    let uu____15049 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____15052 =
                                      let uu____15055 =
                                        FStar_List.map
                                          (fun uu____15070  ->
                                             match uu____15070 with
                                             | (uu____15079,uu____15080,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____15055  in
                                    mk_problem uu____15048 orig uu____15049
                                      (p_rel orig) uu____15052
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_36  ->
                                       FStar_TypeChecker_Common.TProb _0_36)
                                    uu____15043
                                   in
                                ((let uu____15095 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15095
                                  then
                                    let uu____15096 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____15097 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____15096 uu____15097
                                  else ());
                                 (let wl2 =
                                    let uu____15100 =
                                      let uu____15103 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____15103
                                       in
                                    solve_prob orig uu____15100
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____15112 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_37  ->
                                       FStar_Pervasives_Native.Some _0_37)
                                    uu____15112)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____15153 = lhs  in
           match uu____15153 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____15191 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____15191 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____15224 =
                         let uu____15273 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____15273)  in
                       FStar_Pervasives_Native.Some uu____15224
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____15427 =
                            let uu____15434 =
                              let uu____15435 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____15435.FStar_Syntax_Syntax.n  in
                            (uu____15434, args)  in
                          match uu____15427 with
                          | (uu____15446,[]) ->
                              let uu____15449 =
                                let uu____15460 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____15460)  in
                              FStar_Pervasives_Native.Some uu____15449
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____15481,uu____15482) ->
                              let uu____15503 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15503 with
                               | (uv1,uv_args) ->
                                   let uu____15546 =
                                     let uu____15547 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15547.FStar_Syntax_Syntax.n  in
                                   (match uu____15546 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15557) ->
                                        let uu____15582 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15582 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15609  ->
                                                       let uu____15610 =
                                                         let uu____15611 =
                                                           let uu____15612 =
                                                             let uu____15617
                                                               =
                                                               let uu____15618
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15618
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15617
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15612
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15611
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15610))
                                                in
                                             let c1 =
                                               let uu____15628 =
                                                 let uu____15629 =
                                                   let uu____15634 =
                                                     let uu____15635 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15635
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15634
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15629
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15628
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15648 =
                                                 let uu____15651 =
                                                   let uu____15652 =
                                                     let uu____15655 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15655
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15652
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15651
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15648
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15674 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____15679,uu____15680) ->
                              let uu____15699 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15699 with
                               | (uv1,uv_args) ->
                                   let uu____15742 =
                                     let uu____15743 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15743.FStar_Syntax_Syntax.n  in
                                   (match uu____15742 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15753) ->
                                        let uu____15778 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15778 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15805  ->
                                                       let uu____15806 =
                                                         let uu____15807 =
                                                           let uu____15808 =
                                                             let uu____15813
                                                               =
                                                               let uu____15814
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15814
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15813
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15808
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15807
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15806))
                                                in
                                             let c1 =
                                               let uu____15824 =
                                                 let uu____15825 =
                                                   let uu____15830 =
                                                     let uu____15831 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15831
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15830
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15825
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15824
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15844 =
                                                 let uu____15847 =
                                                   let uu____15848 =
                                                     let uu____15851 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15851
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15848
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15847
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15844
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15870 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____15877) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____15918 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____15918
                                  (fun _0_38  ->
                                     FStar_Pervasives_Native.Some _0_38)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____15954 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____15954 with
                                   | (args1,rest) ->
                                       let uu____15983 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____15983 with
                                        | (xs2,c2) ->
                                            let uu____15996 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____15996
                                              (fun uu____16020  ->
                                                 match uu____16020 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____16060 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____16060 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16128 =
                                         let uu____16133 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____16133
                                          in
                                       FStar_All.pipe_right uu____16128
                                         (fun _0_39  ->
                                            FStar_Pervasives_Native.Some
                                              _0_39))
                          | uu____16148 ->
                              let uu____16155 =
                                let uu____16160 =
                                  let uu____16161 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____16162 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____16163 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____16161 uu____16162 uu____16163
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____16160)
                                 in
                              FStar_Errors.raise_error uu____16155
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____16170 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____16170
                          (fun uu____16227  ->
                             match uu____16227 with
                             | (xs1,c1) ->
                                 let uu____16278 =
                                   let uu____16321 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____16321)
                                    in
                                 FStar_Pervasives_Native.Some uu____16278))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____16458 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____16478 = project orig env wl1 i st  in
                      match uu____16478 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____16492) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____16507 = imitate orig env wl1 st  in
                   match uu____16507 with
                   | Failed uu____16512 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____16551 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____16551 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____16574 = forced_lhs_pattern  in
                     (match uu____16574 with
                      | (lhs_t,uu____16576,uu____16577,uu____16578) ->
                          ((let uu____16580 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16580
                            then
                              let uu____16581 = lhs1  in
                              match uu____16581 with
                              | (t0,uu____16583,uu____16584,uu____16585) ->
                                  let uu____16586 = forced_lhs_pattern  in
                                  (match uu____16586 with
                                   | (t11,uu____16588,uu____16589,uu____16590)
                                       ->
                                       let uu____16591 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____16592 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____16591 uu____16592)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____16600 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____16600
                            then
                              ((let uu____16602 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16602
                                then
                                  let uu____16603 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____16604 = names_to_string rhs_vars
                                     in
                                  let uu____16605 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____16603 uu____16604 uu____16605
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____16609 =
                                  let uu____16610 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____16610 wl2  in
                                match uu____16609 with
                                | Failed uu____16611 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____16620 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16620
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____16637 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____16637 with
                 | (hd1,uu____16653) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____16674 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____16687 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____16688 -> true
                      | uu____16705 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____16709 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____16709
                          then true
                          else
                            ((let uu____16712 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____16712
                              then
                                let uu____16713 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____16713
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
                    let uu____16733 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____16733 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____16746 =
                             let uu____16747 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____16747
                              in
                           giveup_or_defer1 orig uu____16746
                         else
                           (let uu____16749 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____16749
                            then
                              let uu____16750 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____16750
                               then
                                 let uu____16751 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____16751
                               else
                                 ((let uu____16756 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____16756
                                   then
                                     let uu____16757 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____16758 = names_to_string fvs1
                                        in
                                     let uu____16759 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____16757 uu____16758 uu____16759
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
                                (let uu____16763 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____16763
                                 then
                                   ((let uu____16765 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____16765
                                     then
                                       let uu____16766 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____16767 = names_to_string fvs1
                                          in
                                       let uu____16768 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____16766 uu____16767 uu____16768
                                     else ());
                                    (let uu____16770 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____16770))
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
                      (let uu____16781 =
                         let uu____16782 = FStar_Syntax_Free.names t1  in
                         check_head uu____16782 t2  in
                       if uu____16781
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____16793 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16793
                           then
                             let uu____16794 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____16795 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____16794 uu____16795
                           else ());
                          (let uu____16803 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____16803))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____16894 uu____16895 r =
                match (uu____16894, uu____16895) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____17093 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____17093
                    then
                      let uu____17094 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____17094
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____17118 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____17118
                        then
                          let uu____17119 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____17120 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____17121 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____17122 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____17123 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____17119 uu____17120 uu____17121 uu____17122
                            uu____17123
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____17189 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____17189 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____17203 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____17203 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____17257 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____17257
                                      in
                                   let uu____17260 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____17260 k3)
                            else
                              (let uu____17264 =
                                 let uu____17265 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____17266 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____17267 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____17265 uu____17266 uu____17267
                                  in
                               failwith uu____17264)
                           in
                        let uu____17268 =
                          let uu____17275 =
                            let uu____17288 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____17288  in
                          match uu____17275 with
                          | (bs,k1') ->
                              let uu____17313 =
                                let uu____17326 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____17326
                                 in
                              (match uu____17313 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____17354 =
                                       let uu____17359 = p_scope orig  in
                                       mk_problem uu____17359 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_40  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_40) uu____17354
                                      in
                                   let uu____17364 =
                                     let uu____17369 =
                                       let uu____17370 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____17370.FStar_Syntax_Syntax.n  in
                                     let uu____17373 =
                                       let uu____17374 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____17374.FStar_Syntax_Syntax.n  in
                                     (uu____17369, uu____17373)  in
                                   (match uu____17364 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____17383,uu____17384) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____17387,FStar_Syntax_Syntax.Tm_type
                                       uu____17388) -> (k2'_ys, [sub_prob])
                                    | uu____17391 ->
                                        let uu____17396 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____17396 with
                                         | (t,uu____17408) ->
                                             let uu____17409 =
                                               new_uvar r zs t  in
                                             (match uu____17409 with
                                              | (k_zs,uu____17421) ->
                                                  let kprob =
                                                    let uu____17423 =
                                                      let uu____17428 =
                                                        p_scope orig  in
                                                      mk_problem uu____17428
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_41  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_41) uu____17423
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____17268 with
                        | (k_u',sub_probs) ->
                            let uu____17441 =
                              let uu____17452 =
                                let uu____17453 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____17453
                                 in
                              let uu____17462 =
                                let uu____17465 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____17465  in
                              let uu____17468 =
                                let uu____17471 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____17471  in
                              (uu____17452, uu____17462, uu____17468)  in
                            (match uu____17441 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____17490 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____17490 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____17509 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____17509
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
                                            let uu____17513 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____17513 with
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
              let solve_one_pat uu____17570 uu____17571 =
                match (uu____17570, uu____17571) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____17689 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____17689
                      then
                        let uu____17690 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____17691 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____17690 uu____17691
                      else ());
                     (let uu____17693 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____17693
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____17712  ->
                               fun uu____17713  ->
                                 match (uu____17712, uu____17713) with
                                 | ((a,uu____17731),(t21,uu____17733)) ->
                                     let uu____17742 =
                                       let uu____17747 = p_scope orig  in
                                       let uu____17748 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____17747 orig
                                         uu____17748
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____17742
                                       (fun _0_42  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_42)) xs args2
                           in
                        let guard =
                          let uu____17754 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____17754  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____17769 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____17769 with
                         | (occurs_ok,uu____17777) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____17785 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____17785
                             then
                               let sol =
                                 let uu____17787 =
                                   let uu____17796 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____17796)  in
                                 TERM uu____17787  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____17803 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____17803
                                then
                                  let uu____17804 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____17804 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____17828,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____17854 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____17854
                                        then
                                          let uu____17855 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____17855
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____17862 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____17864 = lhs  in
              match uu____17864 with
              | (t1,u1,k1,args1) ->
                  let uu____17869 = rhs  in
                  (match uu____17869 with
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
                        | uu____17909 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____17919 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____17919 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____17937) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____17944 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____17944
                                     then
                                       let uu____17945 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____17945
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____17952 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17955 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17955
          then
            let uu____17956 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17956
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____17960 = FStar_Util.physical_equality t1 t2  in
             if uu____17960
             then
               let uu____17961 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____17961
             else
               ((let uu____17964 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____17964
                 then
                   let uu____17965 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____17966 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____17967 = FStar_Syntax_Print.tag_of_term t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17965
                     uu____17966 uu____17967
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____17970,uu____17971)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____17996,FStar_Syntax_Syntax.Tm_delayed uu____17997)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____18022,uu____18023)
                     ->
                     let uu____18050 =
                       let uu___150_18051 = problem  in
                       let uu____18052 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_18051.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18052;
                         FStar_TypeChecker_Common.relation =
                           (uu___150_18051.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___150_18051.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___150_18051.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_18051.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_18051.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_18051.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_18051.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_18051.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18050 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____18053,uu____18054) ->
                     let uu____18061 =
                       let uu___151_18062 = problem  in
                       let uu____18063 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_18062.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18063;
                         FStar_TypeChecker_Common.relation =
                           (uu___151_18062.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___151_18062.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___151_18062.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_18062.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_18062.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_18062.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_18062.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_18062.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18061 wl
                 | (uu____18064,FStar_Syntax_Syntax.Tm_ascribed uu____18065)
                     ->
                     let uu____18092 =
                       let uu___152_18093 = problem  in
                       let uu____18094 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_18093.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___152_18093.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___152_18093.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18094;
                         FStar_TypeChecker_Common.element =
                           (uu___152_18093.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_18093.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___152_18093.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_18093.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_18093.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_18093.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18092 wl
                 | (uu____18095,FStar_Syntax_Syntax.Tm_meta uu____18096) ->
                     let uu____18103 =
                       let uu___153_18104 = problem  in
                       let uu____18105 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___153_18104.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___153_18104.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___153_18104.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18105;
                         FStar_TypeChecker_Common.element =
                           (uu___153_18104.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___153_18104.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___153_18104.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___153_18104.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___153_18104.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___153_18104.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18103 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____18107),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____18109)) ->
                     let uu____18118 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____18118
                 | (FStar_Syntax_Syntax.Tm_bvar uu____18119,uu____18120) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____18121,FStar_Syntax_Syntax.Tm_bvar uu____18122) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___114_18181 =
                       match uu___114_18181 with
                       | [] -> c
                       | bs ->
                           let uu____18203 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____18203
                        in
                     let uu____18212 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____18212 with
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
                                     let uu____18356 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____18356
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____18358 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_43  ->
                                        FStar_TypeChecker_Common.CProb _0_43)
                                     uu____18358))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___115_18440 =
                       match uu___115_18440 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18474 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____18474 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____18612 =
                                     let uu____18617 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____18618 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____18617
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____18618
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_44  ->
                                        FStar_TypeChecker_Common.TProb _0_44)
                                     uu____18612))
                 | (FStar_Syntax_Syntax.Tm_abs uu____18623,uu____18624) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18651 -> true
                       | uu____18668 -> false  in
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
                         (let uu____18719 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_18727 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_18727.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_18727.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_18727.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_18727.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_18727.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_18727.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_18727.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_18727.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_18727.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_18727.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_18727.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_18727.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_18727.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_18727.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_18727.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_18727.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_18727.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_18727.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_18727.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_18727.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_18727.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_18727.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_18727.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_18727.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_18727.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_18727.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_18727.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_18727.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_18727.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_18727.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_18727.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_18727.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_18727.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_18727.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18719 with
                          | (uu____18730,ty,uu____18732) ->
                              let uu____18733 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18733)
                        in
                     let uu____18734 =
                       let uu____18751 = maybe_eta t1  in
                       let uu____18758 = maybe_eta t2  in
                       (uu____18751, uu____18758)  in
                     (match uu____18734 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_18800 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18800.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_18800.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18800.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18800.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18800.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18800.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18800.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18800.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18823 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18823
                          then
                            let uu____18824 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18824 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18839 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18839.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18839.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18839.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18839.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18839.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18839.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18839.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18839.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18863 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18863
                          then
                            let uu____18864 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18864 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18879 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18879.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18879.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18879.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18879.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18879.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18879.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18879.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18879.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18883 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____18900,FStar_Syntax_Syntax.Tm_abs uu____18901) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18928 -> true
                       | uu____18945 -> false  in
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
                         (let uu____18996 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_19004 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_19004.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_19004.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_19004.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_19004.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_19004.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_19004.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_19004.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_19004.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_19004.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_19004.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_19004.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_19004.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_19004.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_19004.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_19004.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_19004.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_19004.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_19004.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_19004.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_19004.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_19004.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_19004.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_19004.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_19004.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_19004.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_19004.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_19004.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_19004.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_19004.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_19004.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_19004.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_19004.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_19004.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_19004.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18996 with
                          | (uu____19007,ty,uu____19009) ->
                              let uu____19010 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____19010)
                        in
                     let uu____19011 =
                       let uu____19028 = maybe_eta t1  in
                       let uu____19035 = maybe_eta t2  in
                       (uu____19028, uu____19035)  in
                     (match uu____19011 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_19077 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_19077.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_19077.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_19077.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_19077.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_19077.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_19077.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_19077.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_19077.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19100 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19100
                          then
                            let uu____19101 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19101 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19116 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19116.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19116.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19116.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19116.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19116.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19116.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19116.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19116.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19140 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19140
                          then
                            let uu____19141 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19141 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19156 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19156.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19156.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19156.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19156.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19156.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19156.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19156.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19156.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19160 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____19192 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____19192) &&
                          (let uu____19204 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____19204))
                         &&
                         (let uu____19219 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____19219 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___116_19231 =
                                match uu___116_19231 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____19232 -> true
                                | uu____19233 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____19234 -> false)
                        in
                     let uu____19235 = as_refinement should_delta env wl t1
                        in
                     (match uu____19235 with
                      | (x11,phi1) ->
                          let uu____19242 =
                            as_refinement should_delta env wl t2  in
                          (match uu____19242 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____19250 =
                                   let uu____19255 = p_scope orig  in
                                   mk_problem uu____19255 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_45  ->
                                      FStar_TypeChecker_Common.TProb _0_45)
                                   uu____19250
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
                                 let uu____19295 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____19295
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____19301 =
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
                                   let uu____19307 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19307 impl
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
                                   let uu____19316 =
                                     let uu____19321 =
                                       let uu____19322 = p_scope orig  in
                                       let uu____19329 =
                                         let uu____19336 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____19336]  in
                                       FStar_List.append uu____19322
                                         uu____19329
                                        in
                                     mk_problem uu____19321 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_46  ->
                                        FStar_TypeChecker_Common.TProb _0_46)
                                     uu____19316
                                    in
                                 let uu____19345 =
                                   solve env1
                                     (let uu___157_19347 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___157_19347.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___157_19347.smt_ok);
                                        tcenv = (uu___157_19347.tcenv)
                                      })
                                    in
                                 (match uu____19345 with
                                  | Failed uu____19354 -> fallback ()
                                  | Success uu____19359 ->
                                      let guard =
                                        let uu____19363 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____19368 =
                                          let uu____19369 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____19369
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____19363
                                          uu____19368
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___158_19378 = wl1  in
                                        {
                                          attempting =
                                            (uu___158_19378.attempting);
                                          wl_deferred =
                                            (uu___158_19378.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___158_19378.defer_ok);
                                          smt_ok = (uu___158_19378.smt_ok);
                                          tcenv = (uu___158_19378.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19380,FStar_Syntax_Syntax.Tm_uvar uu____19381) ->
                     let uu____19414 = destruct_flex_t t1  in
                     let uu____19415 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19414 uu____19415
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19416;
                       FStar_Syntax_Syntax.pos = uu____19417;
                       FStar_Syntax_Syntax.vars = uu____19418;_},uu____19419),FStar_Syntax_Syntax.Tm_uvar
                    uu____19420) ->
                     let uu____19473 = destruct_flex_t t1  in
                     let uu____19474 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19473 uu____19474
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19475,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19476;
                       FStar_Syntax_Syntax.pos = uu____19477;
                       FStar_Syntax_Syntax.vars = uu____19478;_},uu____19479))
                     ->
                     let uu____19532 = destruct_flex_t t1  in
                     let uu____19533 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19532 uu____19533
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19534;
                       FStar_Syntax_Syntax.pos = uu____19535;
                       FStar_Syntax_Syntax.vars = uu____19536;_},uu____19537),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19538;
                       FStar_Syntax_Syntax.pos = uu____19539;
                       FStar_Syntax_Syntax.vars = uu____19540;_},uu____19541))
                     ->
                     let uu____19614 = destruct_flex_t t1  in
                     let uu____19615 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19614 uu____19615
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19616,uu____19617) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19634 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19634 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19641;
                       FStar_Syntax_Syntax.pos = uu____19642;
                       FStar_Syntax_Syntax.vars = uu____19643;_},uu____19644),uu____19645)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19682 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19682 t2 wl
                 | (uu____19689,FStar_Syntax_Syntax.Tm_uvar uu____19690) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____19707,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19708;
                       FStar_Syntax_Syntax.pos = uu____19709;
                       FStar_Syntax_Syntax.vars = uu____19710;_},uu____19711))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19748,FStar_Syntax_Syntax.Tm_type uu____19749) ->
                     solve_t' env
                       (let uu___159_19767 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19767.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19767.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19767.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19767.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19767.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19767.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19767.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19767.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19767.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19768;
                       FStar_Syntax_Syntax.pos = uu____19769;
                       FStar_Syntax_Syntax.vars = uu____19770;_},uu____19771),FStar_Syntax_Syntax.Tm_type
                    uu____19772) ->
                     solve_t' env
                       (let uu___159_19810 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19810.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19810.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19810.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19810.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19810.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19810.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19810.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19810.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19810.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19811,FStar_Syntax_Syntax.Tm_arrow uu____19812) ->
                     solve_t' env
                       (let uu___159_19842 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19842.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19842.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19842.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19842.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19842.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19842.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19842.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19842.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19842.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19843;
                       FStar_Syntax_Syntax.pos = uu____19844;
                       FStar_Syntax_Syntax.vars = uu____19845;_},uu____19846),FStar_Syntax_Syntax.Tm_arrow
                    uu____19847) ->
                     solve_t' env
                       (let uu___159_19897 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19897.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19897.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19897.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19897.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19897.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19897.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19897.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19897.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19897.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19898,uu____19899) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19918 =
                          let uu____19919 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19919
                           in
                        if uu____19918
                        then
                          let uu____19920 =
                            FStar_All.pipe_left
                              (fun _0_47  ->
                                 FStar_TypeChecker_Common.TProb _0_47)
                              (let uu___160_19926 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_19926.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_19926.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_19926.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_19926.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_19926.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_19926.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_19926.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_19926.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_19926.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19927 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19920 uu____19927 t2
                            wl
                        else
                          (let uu____19935 = base_and_refinement env t2  in
                           match uu____19935 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19964 =
                                      FStar_All.pipe_left
                                        (fun _0_48  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_48)
                                        (let uu___161_19970 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_19970.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_19970.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_19970.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_19970.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_19970.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_19970.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_19970.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_19970.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_19970.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19971 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19964
                                      uu____19971 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_19985 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_19985.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_19985.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19988 =
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
                                             _0_49) uu____19988
                                       in
                                    let guard =
                                      let uu____20000 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20000
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
                         uu____20008;
                       FStar_Syntax_Syntax.pos = uu____20009;
                       FStar_Syntax_Syntax.vars = uu____20010;_},uu____20011),uu____20012)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20051 =
                          let uu____20052 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20052
                           in
                        if uu____20051
                        then
                          let uu____20053 =
                            FStar_All.pipe_left
                              (fun _0_50  ->
                                 FStar_TypeChecker_Common.TProb _0_50)
                              (let uu___160_20059 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_20059.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_20059.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_20059.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_20059.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_20059.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_20059.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_20059.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_20059.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_20059.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20060 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20053 uu____20060 t2
                            wl
                        else
                          (let uu____20068 = base_and_refinement env t2  in
                           match uu____20068 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20097 =
                                      FStar_All.pipe_left
                                        (fun _0_51  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_51)
                                        (let uu___161_20103 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_20103.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_20103.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_20103.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_20103.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_20103.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_20103.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_20103.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_20103.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_20103.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20104 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20097
                                      uu____20104 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_20118 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_20118.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_20118.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20121 =
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
                                             _0_52) uu____20121
                                       in
                                    let guard =
                                      let uu____20133 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20133
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____20141,FStar_Syntax_Syntax.Tm_uvar uu____20142) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20160 = base_and_refinement env t1  in
                        match uu____20160 with
                        | (t_base,uu____20172) ->
                            solve_t env
                              (let uu___163_20186 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20186.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20186.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20186.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20186.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20186.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20186.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20186.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20186.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____20187,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20188;
                       FStar_Syntax_Syntax.pos = uu____20189;
                       FStar_Syntax_Syntax.vars = uu____20190;_},uu____20191))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20229 = base_and_refinement env t1  in
                        match uu____20229 with
                        | (t_base,uu____20241) ->
                            solve_t env
                              (let uu___163_20255 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20255.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20255.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20255.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20255.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20255.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20255.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20255.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20255.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____20256,uu____20257) ->
                     let t21 =
                       let uu____20267 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____20267  in
                     solve_t env
                       (let uu___164_20291 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___164_20291.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___164_20291.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___164_20291.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___164_20291.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___164_20291.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___164_20291.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___164_20291.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___164_20291.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___164_20291.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____20292,FStar_Syntax_Syntax.Tm_refine uu____20293) ->
                     let t11 =
                       let uu____20303 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____20303  in
                     solve_t env
                       (let uu___165_20327 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_20327.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_20327.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_20327.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_20327.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_20327.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_20327.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_20327.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_20327.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_20327.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                     let sc_prob =
                       let uu____20407 =
                         let uu____20412 = p_scope orig  in
                         mk_problem uu____20412 orig t11
                           FStar_TypeChecker_Common.EQ t21
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_TypeChecker_Common.TProb _0_53)
                         uu____20407
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____20602 = br1  in
                           (match uu____20602 with
                            | (p1,w1,uu____20621) ->
                                let uu____20634 = br2  in
                                (match uu____20634 with
                                 | (p2,w2,uu____20649) ->
                                     let uu____20654 =
                                       let uu____20655 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____20655  in
                                     if uu____20654
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____20663 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____20663 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____20706 = br2  in
                                            (match uu____20706 with
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
                                                   let uu____20737 =
                                                     p_scope orig  in
                                                   let uu____20744 =
                                                     let uu____20751 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____20751
                                                      in
                                                   FStar_List.append
                                                     uu____20737 uu____20744
                                                    in
                                                 let uu____20762 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____20777,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____20790) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____20823 =
                                                         let uu____20826 =
                                                           let uu____20827 =
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
                                                             uu____20827
                                                            in
                                                         [uu____20826]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20823
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____20762
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____20851 =
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
                                                          uu____20851
                                                         in
                                                      let uu____20862 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____20862
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____20923 -> FStar_Pervasives_Native.None  in
                     let uu____20954 = solve_branches brs1 brs2  in
                     (match uu____20954 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let wl1 =
                            solve_prob orig FStar_Pervasives_Native.None []
                              wl
                             in
                          solve env (attempt sub_probs1 wl1))
                 | (FStar_Syntax_Syntax.Tm_match uu____20970,uu____20971) ->
                     let head1 =
                       let uu____20997 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20997
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21041 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21041
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21083 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21083
                       then
                         let uu____21084 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21085 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21086 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21084 uu____21085 uu____21086
                       else ());
                      (let uu____21088 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21088
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21103 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21103
                          then
                            let guard =
                              let uu____21115 =
                                let uu____21116 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21116 = FStar_Syntax_Util.Equal  in
                              if uu____21115
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21120 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   uu____21120)
                               in
                            let uu____21123 = solve_prob orig guard [] wl  in
                            solve env uu____21123
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____21126,uu____21127) ->
                     let head1 =
                       let uu____21137 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21137
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21181 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21181
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21223 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21223
                       then
                         let uu____21224 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21225 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21226 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21224 uu____21225 uu____21226
                       else ());
                      (let uu____21228 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21228
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21243 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21243
                          then
                            let guard =
                              let uu____21255 =
                                let uu____21256 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21256 = FStar_Syntax_Util.Equal  in
                              if uu____21255
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21260 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   uu____21260)
                               in
                            let uu____21263 = solve_prob orig guard [] wl  in
                            solve env uu____21263
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____21266,uu____21267) ->
                     let head1 =
                       let uu____21271 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21271
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21315 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21315
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21357 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21357
                       then
                         let uu____21358 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21359 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21360 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21358 uu____21359 uu____21360
                       else ());
                      (let uu____21362 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21362
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21377 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21377
                          then
                            let guard =
                              let uu____21389 =
                                let uu____21390 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21390 = FStar_Syntax_Util.Equal  in
                              if uu____21389
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21394 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_Pervasives_Native.Some _0_58)
                                   uu____21394)
                               in
                            let uu____21397 = solve_prob orig guard [] wl  in
                            solve env uu____21397
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____21400,uu____21401)
                     ->
                     let head1 =
                       let uu____21405 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21405
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21449 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21449
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21491 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21491
                       then
                         let uu____21492 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21493 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21494 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21492 uu____21493 uu____21494
                       else ());
                      (let uu____21496 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21496
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21511 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21511
                          then
                            let guard =
                              let uu____21523 =
                                let uu____21524 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21524 = FStar_Syntax_Util.Equal  in
                              if uu____21523
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21528 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_Pervasives_Native.Some _0_59)
                                   uu____21528)
                               in
                            let uu____21531 = solve_prob orig guard [] wl  in
                            solve env uu____21531
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____21534,uu____21535) ->
                     let head1 =
                       let uu____21539 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21539
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21583 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21583
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21625 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21625
                       then
                         let uu____21626 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21627 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21628 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21626 uu____21627 uu____21628
                       else ());
                      (let uu____21630 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21630
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21645 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21645
                          then
                            let guard =
                              let uu____21657 =
                                let uu____21658 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21658 = FStar_Syntax_Util.Equal  in
                              if uu____21657
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21662 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____21662)
                               in
                            let uu____21665 = solve_prob orig guard [] wl  in
                            solve env uu____21665
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____21668,uu____21669) ->
                     let head1 =
                       let uu____21687 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21687
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21731 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21731
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21773 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21773
                       then
                         let uu____21774 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21775 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21776 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21774 uu____21775 uu____21776
                       else ());
                      (let uu____21778 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21778
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21793 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21793
                          then
                            let guard =
                              let uu____21805 =
                                let uu____21806 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21806 = FStar_Syntax_Util.Equal  in
                              if uu____21805
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21810 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____21810)
                               in
                            let uu____21813 = solve_prob orig guard [] wl  in
                            solve env uu____21813
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21816,FStar_Syntax_Syntax.Tm_match uu____21817) ->
                     let head1 =
                       let uu____21843 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21843
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21887 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21887
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21929 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21929
                       then
                         let uu____21930 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21931 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21932 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21930 uu____21931 uu____21932
                       else ());
                      (let uu____21934 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21934
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21949 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21949
                          then
                            let guard =
                              let uu____21961 =
                                let uu____21962 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21962 = FStar_Syntax_Util.Equal  in
                              if uu____21961
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21966 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____21966)
                               in
                            let uu____21969 = solve_prob orig guard [] wl  in
                            solve env uu____21969
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21972,FStar_Syntax_Syntax.Tm_uinst uu____21973) ->
                     let head1 =
                       let uu____21983 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21983
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22027 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22027
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22069 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22069
                       then
                         let uu____22070 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22071 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22072 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22070 uu____22071 uu____22072
                       else ());
                      (let uu____22074 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22074
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22089 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22089
                          then
                            let guard =
                              let uu____22101 =
                                let uu____22102 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22102 = FStar_Syntax_Util.Equal  in
                              if uu____22101
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22106 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   uu____22106)
                               in
                            let uu____22109 = solve_prob orig guard [] wl  in
                            solve env uu____22109
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22112,FStar_Syntax_Syntax.Tm_name uu____22113) ->
                     let head1 =
                       let uu____22117 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22117
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22161 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22161
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22203 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22203
                       then
                         let uu____22204 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22205 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22206 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22204 uu____22205 uu____22206
                       else ());
                      (let uu____22208 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22208
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22223 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22223
                          then
                            let guard =
                              let uu____22235 =
                                let uu____22236 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22236 = FStar_Syntax_Util.Equal  in
                              if uu____22235
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22240 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   uu____22240)
                               in
                            let uu____22243 = solve_prob orig guard [] wl  in
                            solve env uu____22243
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22246,FStar_Syntax_Syntax.Tm_constant uu____22247)
                     ->
                     let head1 =
                       let uu____22251 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22251
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22295 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22295
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22337 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22337
                       then
                         let uu____22338 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22339 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22340 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22338 uu____22339 uu____22340
                       else ());
                      (let uu____22342 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22342
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22357 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22357
                          then
                            let guard =
                              let uu____22369 =
                                let uu____22370 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22370 = FStar_Syntax_Util.Equal  in
                              if uu____22369
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22374 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   uu____22374)
                               in
                            let uu____22377 = solve_prob orig guard [] wl  in
                            solve env uu____22377
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22380,FStar_Syntax_Syntax.Tm_fvar uu____22381) ->
                     let head1 =
                       let uu____22385 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22385
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22429 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22429
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22471 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22471
                       then
                         let uu____22472 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22473 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22474 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22472 uu____22473 uu____22474
                       else ());
                      (let uu____22476 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22476
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22491 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22491
                          then
                            let guard =
                              let uu____22503 =
                                let uu____22504 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22504 = FStar_Syntax_Util.Equal  in
                              if uu____22503
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22508 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   uu____22508)
                               in
                            let uu____22511 = solve_prob orig guard [] wl  in
                            solve env uu____22511
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22514,FStar_Syntax_Syntax.Tm_app uu____22515) ->
                     let head1 =
                       let uu____22533 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22533
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22577 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22577
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22619 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22619
                       then
                         let uu____22620 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22621 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22622 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22620 uu____22621 uu____22622
                       else ());
                      (let uu____22624 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22624
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22639 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22639
                          then
                            let guard =
                              let uu____22651 =
                                let uu____22652 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22652 = FStar_Syntax_Util.Equal  in
                              if uu____22651
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22656 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   uu____22656)
                               in
                            let uu____22659 = solve_prob orig guard [] wl  in
                            solve env uu____22659
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____22662,FStar_Syntax_Syntax.Tm_let uu____22663) ->
                     let uu____22688 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____22688
                     then
                       let uu____22689 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____22689
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____22691,uu____22692) ->
                     let uu____22705 =
                       let uu____22710 =
                         let uu____22711 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22712 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22713 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22714 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22711 uu____22712 uu____22713 uu____22714
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22710)
                        in
                     FStar_Errors.raise_error uu____22705
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____22715,FStar_Syntax_Syntax.Tm_let uu____22716) ->
                     let uu____22729 =
                       let uu____22734 =
                         let uu____22735 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22736 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22737 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22738 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22735 uu____22736 uu____22737 uu____22738
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22734)
                        in
                     FStar_Errors.raise_error uu____22729
                       t1.FStar_Syntax_Syntax.pos
                 | uu____22739 -> giveup env "head tag mismatch" orig)))))

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
          let uu____22775 = p_scope orig  in
          mk_problem uu____22775 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____22788 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____22788
           then
             let uu____22789 =
               let uu____22790 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____22790  in
             let uu____22791 =
               let uu____22792 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____22792  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____22789 uu____22791
           else ());
          (let uu____22794 =
             let uu____22795 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____22795  in
           if uu____22794
           then
             let uu____22796 =
               let uu____22797 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____22798 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____22797 uu____22798
                in
             giveup env uu____22796 orig
           else
             (let ret_sub_prob =
                let uu____22801 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                  uu____22801
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____22828  ->
                     fun uu____22829  ->
                       match (uu____22828, uu____22829) with
                       | ((a1,uu____22847),(a2,uu____22849)) ->
                           let uu____22858 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_69  ->
                                FStar_TypeChecker_Common.TProb _0_69)
                             uu____22858)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____22871 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____22871  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22903 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22910)::[] -> wp1
              | uu____22927 ->
                  let uu____22936 =
                    let uu____22937 =
                      let uu____22938 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____22938  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22937
                     in
                  failwith uu____22936
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____22946 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____22946]
              | x -> x  in
            let uu____22948 =
              let uu____22957 =
                let uu____22958 =
                  let uu____22959 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____22959 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____22958  in
              [uu____22957]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22948;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22960 = lift_c1 ()  in solve_eq uu____22960 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_22966  ->
                       match uu___117_22966 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22967 -> false))
                in
             let uu____22968 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23002)::uu____23003,(wp2,uu____23005)::uu____23006)
                   -> (wp1, wp2)
               | uu____23063 ->
                   let uu____23084 =
                     let uu____23089 =
                       let uu____23090 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23091 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23090 uu____23091
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23089)
                      in
                   FStar_Errors.raise_error uu____23084
                     env.FStar_TypeChecker_Env.range
                in
             match uu____22968 with
             | (wpc1,wpc2) ->
                 let uu____23110 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23110
                 then
                   let uu____23113 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23113 wl
                 else
                   (let uu____23117 =
                      let uu____23124 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23124  in
                    match uu____23117 with
                    | (c2_decl,qualifiers) ->
                        let uu____23145 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23145
                        then
                          let c1_repr =
                            let uu____23149 =
                              let uu____23150 =
                                let uu____23151 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23151  in
                              let uu____23152 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23150 uu____23152
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23149
                             in
                          let c2_repr =
                            let uu____23154 =
                              let uu____23155 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23156 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23155 uu____23156
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23154
                             in
                          let prob =
                            let uu____23158 =
                              let uu____23163 =
                                let uu____23164 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____23165 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23164
                                  uu____23165
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23163
                               in
                            FStar_TypeChecker_Common.TProb uu____23158  in
                          let wl1 =
                            let uu____23167 =
                              let uu____23170 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____23170  in
                            solve_prob orig uu____23167 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23179 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23179
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23182 =
                                     let uu____23189 =
                                       let uu____23190 =
                                         let uu____23205 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23206 =
                                           let uu____23209 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23210 =
                                             let uu____23213 =
                                               let uu____23214 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23214
                                                in
                                             [uu____23213]  in
                                           uu____23209 :: uu____23210  in
                                         (uu____23205, uu____23206)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23190
                                        in
                                     FStar_Syntax_Syntax.mk uu____23189  in
                                   uu____23182 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23223 =
                                    let uu____23230 =
                                      let uu____23231 =
                                        let uu____23246 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23247 =
                                          let uu____23250 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____23251 =
                                            let uu____23254 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____23255 =
                                              let uu____23258 =
                                                let uu____23259 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23259
                                                 in
                                              [uu____23258]  in
                                            uu____23254 :: uu____23255  in
                                          uu____23250 :: uu____23251  in
                                        (uu____23246, uu____23247)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23231
                                       in
                                    FStar_Syntax_Syntax.mk uu____23230  in
                                  uu____23223 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23266 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____23266
                              in
                           let wl1 =
                             let uu____23276 =
                               let uu____23279 =
                                 let uu____23282 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23282 g  in
                               FStar_All.pipe_left
                                 (fun _0_71  ->
                                    FStar_Pervasives_Native.Some _0_71)
                                 uu____23279
                                in
                             solve_prob orig uu____23276 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23295 = FStar_Util.physical_equality c1 c2  in
        if uu____23295
        then
          let uu____23296 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23296
        else
          ((let uu____23299 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23299
            then
              let uu____23300 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____23301 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23300
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23301
            else ());
           (let uu____23303 =
              let uu____23308 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____23309 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____23308, uu____23309)  in
            match uu____23303 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23313),FStar_Syntax_Syntax.Total
                    (t2,uu____23315)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23332 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23332 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23335,FStar_Syntax_Syntax.Total uu____23336) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23354),FStar_Syntax_Syntax.Total
                    (t2,uu____23356)) ->
                     let uu____23373 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23373 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23377),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23379)) ->
                     let uu____23396 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23396 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23400),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23402)) ->
                     let uu____23419 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23419 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23422,FStar_Syntax_Syntax.Comp uu____23423) ->
                     let uu____23432 =
                       let uu___166_23437 = problem  in
                       let uu____23442 =
                         let uu____23443 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23443
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23437.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23442;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23437.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23437.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23437.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23437.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23437.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23437.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23437.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23437.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23432 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23444,FStar_Syntax_Syntax.Comp uu____23445) ->
                     let uu____23454 =
                       let uu___166_23459 = problem  in
                       let uu____23464 =
                         let uu____23465 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23465
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23459.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23464;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23459.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23459.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23459.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23459.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23459.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23459.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23459.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23459.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23454 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23466,FStar_Syntax_Syntax.GTotal uu____23467) ->
                     let uu____23476 =
                       let uu___167_23481 = problem  in
                       let uu____23486 =
                         let uu____23487 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23487
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23481.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23481.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23481.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23486;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23481.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23481.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23481.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23481.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23481.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23481.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23476 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23488,FStar_Syntax_Syntax.Total uu____23489) ->
                     let uu____23498 =
                       let uu___167_23503 = problem  in
                       let uu____23508 =
                         let uu____23509 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23509
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23503.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23503.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23503.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23508;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23503.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23503.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23503.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23503.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23503.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23503.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23498 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23510,FStar_Syntax_Syntax.Comp uu____23511) ->
                     let uu____23512 =
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
                     if uu____23512
                     then
                       let uu____23513 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____23513 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____23519 =
                            let uu____23524 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____23524
                            then (c1_comp, c2_comp)
                            else
                              (let uu____23530 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____23531 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____23530, uu____23531))
                             in
                          match uu____23519 with
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
                           (let uu____23538 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23538
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23540 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____23540 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23543 =
                                  let uu____23544 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____23545 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____23544 uu____23545
                                   in
                                giveup env uu____23543 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23552 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23590  ->
              match uu____23590 with
              | (uu____23603,uu____23604,u,uu____23606,uu____23607,uu____23608)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23552 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____23641 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____23641 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____23659 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23687  ->
                match uu____23687 with
                | (u1,u2) ->
                    let uu____23694 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____23695 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____23694 uu____23695))
         in
      FStar_All.pipe_right uu____23659 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23716,[])) -> "{}"
      | uu____23741 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23758 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____23758
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23761 =
              FStar_List.map
                (fun uu____23771  ->
                   match uu____23771 with
                   | (uu____23776,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23761 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23781 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23781 imps
  
let new_t_problem :
  'Auu____23796 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____23796 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____23796)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____23836 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____23836
                then
                  let uu____23837 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____23838 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23837
                    (rel_to_string rel) uu____23838
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
            let uu____23870 =
              let uu____23873 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_72  -> FStar_Pervasives_Native.Some _0_72)
                uu____23873
               in
            FStar_Syntax_Syntax.new_bv uu____23870 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____23882 =
              let uu____23885 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_73  -> FStar_Pervasives_Native.Some _0_73)
                uu____23885
               in
            let uu____23888 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____23882 uu____23888  in
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
          let uu____23924 = FStar_Options.eager_inference ()  in
          if uu____23924
          then
            let uu___168_23925 = probs  in
            {
              attempting = (uu___168_23925.attempting);
              wl_deferred = (uu___168_23925.wl_deferred);
              ctr = (uu___168_23925.ctr);
              defer_ok = false;
              smt_ok = (uu___168_23925.smt_ok);
              tcenv = (uu___168_23925.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____23936 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____23936
              then
                let uu____23937 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____23937
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
          ((let uu____23955 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23955
            then
              let uu____23956 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23956
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____23960 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____23960
             then
               let uu____23961 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____23961
             else ());
            (let f2 =
               let uu____23964 =
                 let uu____23965 = FStar_Syntax_Util.unmeta f1  in
                 uu____23965.FStar_Syntax_Syntax.n  in
               match uu____23964 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____23969 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___169_23970 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___169_23970.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_23970.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_23970.FStar_TypeChecker_Env.implicits)
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
            let uu____23995 =
              let uu____23996 =
                let uu____23997 =
                  let uu____23998 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____23998
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____23997;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____23996  in
            FStar_All.pipe_left
              (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____23995
  
let with_guard_no_simp :
  'Auu____24029 .
    'Auu____24029 ->
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
            let uu____24052 =
              let uu____24053 =
                let uu____24054 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____24054
                  (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24053;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24052
  
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
          (let uu____24100 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24100
           then
             let uu____24101 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24102 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24101
               uu____24102
           else ());
          (let prob =
             let uu____24105 =
               let uu____24110 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24110
                in
             FStar_All.pipe_left
               (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
               uu____24105
              in
           let g =
             let uu____24118 =
               let uu____24121 = singleton' env prob smt_ok  in
               solve_and_commit env uu____24121
                 (fun uu____24123  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____24118  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24147 = try_teq true env t1 t2  in
        match uu____24147 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____24151 = FStar_TypeChecker_Env.get_range env  in
              let uu____24152 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____24151 uu____24152);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24159 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____24159
              then
                let uu____24160 = FStar_Syntax_Print.term_to_string t1  in
                let uu____24161 = FStar_Syntax_Print.term_to_string t2  in
                let uu____24162 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24160
                  uu____24161 uu____24162
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
          let uu____24184 = FStar_TypeChecker_Env.get_range env  in
          let uu____24185 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____24184 uu____24185
  
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
        (let uu____24210 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24210
         then
           let uu____24211 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____24212 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____24211 uu____24212
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____24216 =
             let uu____24221 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24221 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____24216
            in
         let uu____24226 =
           let uu____24229 = singleton env prob  in
           solve_and_commit env uu____24229
             (fun uu____24231  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____24226)
  
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
      fun uu____24266  ->
        match uu____24266 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24309 =
                 let uu____24314 =
                   let uu____24315 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____24316 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____24315 uu____24316
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____24314)  in
               let uu____24317 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____24309 uu____24317)
               in
            let equiv1 v1 v' =
              let uu____24329 =
                let uu____24334 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24335 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24334, uu____24335)  in
              match uu____24329 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24354 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24384 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24384 with
                      | FStar_Syntax_Syntax.U_unif uu____24391 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24420  ->
                                    match uu____24420 with
                                    | (u,v') ->
                                        let uu____24429 = equiv1 v1 v'  in
                                        if uu____24429
                                        then
                                          let uu____24432 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24432 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24448 -> []))
               in
            let uu____24453 =
              let wl =
                let uu___170_24457 = empty_worklist env  in
                {
                  attempting = (uu___170_24457.attempting);
                  wl_deferred = (uu___170_24457.wl_deferred);
                  ctr = (uu___170_24457.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_24457.smt_ok);
                  tcenv = (uu___170_24457.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24475  ->
                      match uu____24475 with
                      | (lb,v1) ->
                          let uu____24482 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24482 with
                           | USolved wl1 -> ()
                           | uu____24484 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24494 =
              match uu____24494 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24503) -> true
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
                      uu____24526,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24528,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24539) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24546,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24554 -> false)
               in
            let uu____24559 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24574  ->
                      match uu____24574 with
                      | (u,v1) ->
                          let uu____24581 = check_ineq (u, v1)  in
                          if uu____24581
                          then true
                          else
                            ((let uu____24584 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24584
                              then
                                let uu____24585 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24586 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24585
                                  uu____24586
                              else ());
                             false)))
               in
            if uu____24559
            then ()
            else
              ((let uu____24590 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____24590
                then
                  ((let uu____24592 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24592);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24602 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24602))
                else ());
               (let uu____24612 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____24612))
  
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
      let fail1 uu____24670 =
        match uu____24670 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____24684 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____24684
       then
         let uu____24685 = wl_to_string wl  in
         let uu____24686 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____24685 uu____24686
       else ());
      (let g1 =
         let uu____24701 = solve_and_commit env wl fail1  in
         match uu____24701 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___171_24714 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___171_24714.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_24714.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_24714.FStar_TypeChecker_Env.implicits)
             }
         | uu____24719 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___172_24723 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_24723.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_24723.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___172_24723.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____24751 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24751 with
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
            let uu___173_24874 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___173_24874.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___173_24874.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___173_24874.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24875 =
            let uu____24876 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24876  in
          if uu____24875
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____24884 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24885 =
                       let uu____24886 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24886
                        in
                     FStar_Errors.diag uu____24884 uu____24885)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____24890 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____24891 =
                        let uu____24892 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____24892
                         in
                      FStar_Errors.diag uu____24890 uu____24891)
                   else ();
                   (let uu____24895 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____24895 "discharge_guard'"
                      env vc1);
                   (let uu____24896 = check_trivial vc1  in
                    match uu____24896 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____24903 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24904 =
                                let uu____24905 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____24905
                                 in
                              FStar_Errors.diag uu____24903 uu____24904)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____24910 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24911 =
                                let uu____24912 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____24912
                                 in
                              FStar_Errors.diag uu____24910 uu____24911)
                           else ();
                           (let vcs =
                              let uu____24923 = FStar_Options.use_tactics ()
                                 in
                              if uu____24923
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____24943  ->
                                     (let uu____24945 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a239  -> ())
                                        uu____24945);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____24988  ->
                                              match uu____24988 with
                                              | (env1,goal,opts) ->
                                                  let uu____25004 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____25004, opts)))))
                              else
                                (let uu____25006 =
                                   let uu____25013 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____25013)  in
                                 [uu____25006])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25046  ->
                                    match uu____25046 with
                                    | (env1,goal,opts) ->
                                        let uu____25056 = check_trivial goal
                                           in
                                        (match uu____25056 with
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
                                                (let uu____25064 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25065 =
                                                   let uu____25066 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25067 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25066 uu____25067
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25064 uu____25065)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25070 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25071 =
                                                   let uu____25072 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25072
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25070 uu____25071)
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
      let uu____25086 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25086 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____25093 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____25093
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25104 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____25104 with
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
          let uu____25132 = FStar_Syntax_Unionfind.find u  in
          match uu____25132 with
          | FStar_Pervasives_Native.None  -> true
          | uu____25135 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____25157 = acc  in
          match uu____25157 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____25243 = hd1  in
                   (match uu____25243 with
                    | (uu____25256,env,u,tm,k,r) ->
                        let uu____25262 = unresolved u  in
                        if uu____25262
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___174_25292 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___174_25292.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___174_25292.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___174_25292.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___174_25292.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___174_25292.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___174_25292.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___174_25292.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___174_25292.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___174_25292.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___174_25292.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___174_25292.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___174_25292.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___174_25292.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___174_25292.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___174_25292.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___174_25292.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___174_25292.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___174_25292.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___174_25292.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___174_25292.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___174_25292.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___174_25292.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___174_25292.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___174_25292.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___174_25292.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___174_25292.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___174_25292.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___174_25292.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___174_25292.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___174_25292.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___174_25292.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___174_25292.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___174_25292.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___174_25292.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___174_25292.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___174_25292.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____25295 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____25295
                            then
                              let uu____25296 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____25297 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____25298 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____25296 uu____25297 uu____25298
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____25309 =
                                      let uu____25318 =
                                        let uu____25325 =
                                          let uu____25326 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____25327 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____25326 uu____25327
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____25325, r)
                                         in
                                      [uu____25318]  in
                                    FStar_Errors.add_errors uu____25309);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___177_25341 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___177_25341.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___177_25341.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___177_25341.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____25344 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25351  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____25344 with
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
        let uu___178_25379 = g  in
        let uu____25380 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___178_25379.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___178_25379.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___178_25379.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25380
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
        let uu____25442 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25442 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25455 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a240  -> ()) uu____25455
      | (reason,uu____25457,uu____25458,e,t,r)::uu____25462 ->
          let uu____25489 =
            let uu____25494 =
              let uu____25495 = FStar_Syntax_Print.term_to_string t  in
              let uu____25496 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25495 uu____25496
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25494)
             in
          FStar_Errors.raise_error uu____25489 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___179_25507 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_25507.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_25507.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_25507.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25534 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25534 with
      | FStar_Pervasives_Native.Some uu____25540 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25556 = try_teq false env t1 t2  in
        match uu____25556 with
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
        (let uu____25582 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25582
         then
           let uu____25583 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25584 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25583
             uu____25584
         else ());
        (let uu____25586 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25586 with
         | (prob,x) ->
             let g =
               let uu____25602 =
                 let uu____25605 = singleton' env prob true  in
                 solve_and_commit env uu____25605
                   (fun uu____25607  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25602  in
             ((let uu____25617 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____25617
               then
                 let uu____25618 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____25619 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____25620 =
                   let uu____25621 = FStar_Util.must g  in
                   guard_to_string env uu____25621  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____25618 uu____25619 uu____25620
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
        let uu____25655 = check_subtyping env t1 t2  in
        match uu____25655 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25674 =
              let uu____25675 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____25675 g  in
            FStar_Pervasives_Native.Some uu____25674
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25693 = check_subtyping env t1 t2  in
        match uu____25693 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25712 =
              let uu____25713 =
                let uu____25714 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25714]  in
              close_guard env uu____25713 g  in
            FStar_Pervasives_Native.Some uu____25712
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____25731 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25731
         then
           let uu____25732 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25733 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25732
             uu____25733
         else ());
        (let uu____25735 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25735 with
         | (prob,x) ->
             let g =
               let uu____25745 =
                 let uu____25748 = singleton' env prob false  in
                 solve_and_commit env uu____25748
                   (fun uu____25750  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25745  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____25761 =
                      let uu____25762 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____25762]  in
                    close_guard env uu____25761 g1  in
                  discharge_guard_nosmt env g2))
  