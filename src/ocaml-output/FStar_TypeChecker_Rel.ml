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
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level
                 uu____6422),uu____6423)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6441 =
                     let uu____6450 = maybe_inline t11  in
                     let uu____6453 = maybe_inline t21  in
                     (uu____6450, uu____6453)  in
                   match uu____6441 with
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
                (uu____6490,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6491))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6509 =
                     let uu____6518 = maybe_inline t11  in
                     let uu____6521 = maybe_inline t21  in
                     (uu____6518, uu____6521)  in
                   match uu____6509 with
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
                let uu____6564 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6564 with
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
                let uu____6587 =
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
                (match uu____6587 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6611 -> fail1 r
            | uu____6620 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6633 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6633
           then
             let uu____6634 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6635 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6636 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6634
               uu____6635 uu____6636
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6682 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6726 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___106_6740  ->
    match uu___106_6740 with
    | T (t,uu____6742) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6766 = FStar_Syntax_Util.type_u ()  in
      match uu____6766 with
      | (t,uu____6772) ->
          let uu____6773 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6773
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6788 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6788 FStar_Pervasives_Native.fst
  
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
        let uu____6862 = head_matches env t1 t'  in
        match uu____6862 with
        | MisMatch uu____6863 -> false
        | uu____6872 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6972,imp),T (t2,uu____6975)) -> (t2, imp)
                     | uu____6998 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7065  ->
                    match uu____7065 with
                    | (t2,uu____7079) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7126 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7126 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7211))::tcs2) ->
                       aux
                         (((let uu___131_7250 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_7250.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_7250.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7268 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___107_7325 =
                 match uu___107_7325 with
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
               let uu____7444 = decompose1 [] bs1  in
               (rebuild, matches, uu____7444))
      | uu____7495 ->
          let rebuild uu___108_7503 =
            match uu___108_7503 with
            | [] -> t1
            | uu____7506 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___109_7541  ->
    match uu___109_7541 with
    | T (t,uu____7543) -> t
    | uu____7556 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___110_7561  ->
    match uu___110_7561 with
    | T (t,uu____7563) -> FStar_Syntax_Syntax.as_arg t
    | uu____7576 -> failwith "Impossible"
  
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
              | (uu____7708,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7737 = new_uvar r scope1 k  in
                  (match uu____7737 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7755 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7772 =
                         let uu____7773 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_23  ->
                              FStar_TypeChecker_Common.TProb _0_23)
                           uu____7773
                          in
                       ((T (gi_xs, mk_kind)), uu____7772))
              | (uu____7788,uu____7789,C uu____7790) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7943 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7960;
                         FStar_Syntax_Syntax.vars = uu____7961;_})
                        ->
                        let uu____7984 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7984 with
                         | (T (gi_xs,uu____8010),prob) ->
                             let uu____8024 =
                               let uu____8025 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_24  -> C _0_24)
                                 uu____8025
                                in
                             (uu____8024, [prob])
                         | uu____8028 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____8043;
                         FStar_Syntax_Syntax.vars = uu____8044;_})
                        ->
                        let uu____8067 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8067 with
                         | (T (gi_xs,uu____8093),prob) ->
                             let uu____8107 =
                               let uu____8108 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_25  -> C _0_25)
                                 uu____8108
                                in
                             (uu____8107, [prob])
                         | uu____8111 -> failwith "impossible")
                    | (uu____8122,uu____8123,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8125;
                         FStar_Syntax_Syntax.vars = uu____8126;_})
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
                        let uu____8261 =
                          let uu____8270 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8270 FStar_List.unzip
                           in
                        (match uu____8261 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8324 =
                                 let uu____8325 =
                                   let uu____8328 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8328 un_T  in
                                 let uu____8329 =
                                   let uu____8338 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8338
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8325;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8329;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8324
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8347 ->
                        let uu____8360 = sub_prob scope1 args q  in
                        (match uu____8360 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7943 with
                   | (tc,probs) ->
                       let uu____8391 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8454,uu____8455),T
                            (t,uu____8457)) ->
                             let b1 =
                               ((let uu___132_8498 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___132_8498.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___132_8498.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8499 =
                               let uu____8506 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8506 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8499)
                         | uu____8541 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8391 with
                        | (bopt,scope2,args1) ->
                            let uu____8625 = aux scope2 args1 qs2  in
                            (match uu____8625 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8663 =
                                           let uu____8666 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8666  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8663
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
                                         let uu____8691 =
                                           let uu____8694 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8695 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8694 :: uu____8695  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8691
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
  'Auu____8769 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8769)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8769)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___133_8792 = p  in
      let uu____8797 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8798 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___133_8792.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8797;
        FStar_TypeChecker_Common.relation =
          (uu___133_8792.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8798;
        FStar_TypeChecker_Common.element =
          (uu___133_8792.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___133_8792.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___133_8792.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___133_8792.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___133_8792.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___133_8792.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8814 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8814
            (fun _0_26  -> FStar_TypeChecker_Common.TProb _0_26)
      | FStar_TypeChecker_Common.CProb uu____8823 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8847 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8847 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8857 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8857 with
           | (lh,uu____8877) ->
               let uu____8898 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8898 with
                | (rh,uu____8918) ->
                    let uu____8939 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8956,FStar_Syntax_Syntax.Tm_uvar uu____8957)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8994,uu____8995)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9016,FStar_Syntax_Syntax.Tm_uvar uu____9017)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9038,uu____9039)
                          ->
                          let uu____9056 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9056 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9105 ->
                                    let rank =
                                      let uu____9113 = is_top_level_prob prob
                                         in
                                      if uu____9113
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9115 =
                                      let uu___134_9120 = tp  in
                                      let uu____9125 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___134_9120.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___134_9120.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___134_9120.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9125;
                                        FStar_TypeChecker_Common.element =
                                          (uu___134_9120.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___134_9120.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___134_9120.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___134_9120.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___134_9120.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___134_9120.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9115)))
                      | (uu____9136,FStar_Syntax_Syntax.Tm_uvar uu____9137)
                          ->
                          let uu____9154 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9154 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9203 ->
                                    let uu____9210 =
                                      let uu___135_9217 = tp  in
                                      let uu____9222 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_9217.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9222;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_9217.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___135_9217.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_9217.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_9217.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_9217.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_9217.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_9217.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_9217.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9210)))
                      | (uu____9239,uu____9240) -> (rigid_rigid, tp)  in
                    (match uu____8939 with
                     | (rank,tp1) ->
                         let uu____9259 =
                           FStar_All.pipe_right
                             (let uu___136_9265 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___136_9265.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___136_9265.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___136_9265.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___136_9265.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___136_9265.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___136_9265.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___136_9265.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___136_9265.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___136_9265.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_27  ->
                                FStar_TypeChecker_Common.TProb _0_27)
                            in
                         (rank, uu____9259))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9275 =
            FStar_All.pipe_right
              (let uu___137_9281 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_9281.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_9281.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_9281.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_9281.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_9281.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_9281.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___137_9281.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_9281.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_9281.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_28  -> FStar_TypeChecker_Common.CProb _0_28)
             in
          (rigid_rigid, uu____9275)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9342 probs =
      match uu____9342 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9395 = rank wl hd1  in
               (match uu____9395 with
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
    match projectee with | UDeferred _0 -> true | uu____9511 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9525 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9539 -> false
  
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
                        let uu____9591 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9591 with
                        | (k,uu____9597) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9607 -> false)))
            | uu____9608 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9660 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9666 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9666 = (Prims.parse_int "0")))
                           in
                        if uu____9660 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9682 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9688 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9688 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9682)
               in
            let uu____9689 = filter1 u12  in
            let uu____9692 = filter1 u22  in (uu____9689, uu____9692)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9721 = filter_out_common_univs us1 us2  in
                (match uu____9721 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9780 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9780 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9783 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9793 =
                          let uu____9794 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9795 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9794
                            uu____9795
                           in
                        UFailed uu____9793))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9819 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9819 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9845 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9845 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9848 ->
                let uu____9853 =
                  let uu____9854 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9855 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9854
                    uu____9855 msg
                   in
                UFailed uu____9853
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9856,uu____9857) ->
              let uu____9858 =
                let uu____9859 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9860 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9859 uu____9860
                 in
              failwith uu____9858
          | (FStar_Syntax_Syntax.U_unknown ,uu____9861) ->
              let uu____9862 =
                let uu____9863 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9864 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9863 uu____9864
                 in
              failwith uu____9862
          | (uu____9865,FStar_Syntax_Syntax.U_bvar uu____9866) ->
              let uu____9867 =
                let uu____9868 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9869 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9868 uu____9869
                 in
              failwith uu____9867
          | (uu____9870,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9871 =
                let uu____9872 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9873 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9872 uu____9873
                 in
              failwith uu____9871
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9897 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9897
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9919 = occurs_univ v1 u3  in
              if uu____9919
              then
                let uu____9920 =
                  let uu____9921 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9922 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9921 uu____9922
                   in
                try_umax_components u11 u21 uu____9920
              else
                (let uu____9924 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9924)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9944 = occurs_univ v1 u3  in
              if uu____9944
              then
                let uu____9945 =
                  let uu____9946 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9947 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9946 uu____9947
                   in
                try_umax_components u11 u21 uu____9945
              else
                (let uu____9949 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9949)
          | (FStar_Syntax_Syntax.U_max uu____9958,uu____9959) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9965 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9965
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9967,FStar_Syntax_Syntax.U_max uu____9968) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9974 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9974
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9976,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9977,FStar_Syntax_Syntax.U_name
             uu____9978) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9979) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9980) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9981,FStar_Syntax_Syntax.U_succ
             uu____9982) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9983,FStar_Syntax_Syntax.U_zero
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
      let uu____10083 = bc1  in
      match uu____10083 with
      | (bs1,mk_cod1) ->
          let uu____10127 = bc2  in
          (match uu____10127 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10238 = aux xs ys  in
                     (match uu____10238 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10321 =
                       let uu____10328 = mk_cod1 xs  in ([], uu____10328)  in
                     let uu____10331 =
                       let uu____10338 = mk_cod2 ys  in ([], uu____10338)  in
                     (uu____10321, uu____10331)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10523 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____10523
       then
         let uu____10524 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10524
       else ());
      (let uu____10526 = next_prob probs  in
       match uu____10526 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___138_10547 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___138_10547.wl_deferred);
               ctr = (uu___138_10547.ctr);
               defer_ok = (uu___138_10547.defer_ok);
               smt_ok = (uu___138_10547.smt_ok);
               tcenv = (uu___138_10547.tcenv)
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
                  let uu____10558 = solve_flex_rigid_join env tp probs1  in
                  (match uu____10558 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10563 = solve_rigid_flex_meet env tp probs1
                        in
                     match uu____10563 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10568,uu____10569) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10586 ->
                let uu____10595 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10654  ->
                          match uu____10654 with
                          | (c,uu____10662,uu____10663) -> c < probs.ctr))
                   in
                (match uu____10595 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10704 =
                            FStar_List.map
                              (fun uu____10719  ->
                                 match uu____10719 with
                                 | (uu____10730,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10704
                      | uu____10733 ->
                          let uu____10742 =
                            let uu___139_10743 = probs  in
                            let uu____10744 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10765  ->
                                      match uu____10765 with
                                      | (uu____10772,uu____10773,y) -> y))
                               in
                            {
                              attempting = uu____10744;
                              wl_deferred = rest;
                              ctr = (uu___139_10743.ctr);
                              defer_ok = (uu___139_10743.defer_ok);
                              smt_ok = (uu___139_10743.smt_ok);
                              tcenv = (uu___139_10743.tcenv)
                            }  in
                          solve env uu____10742))))

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
            let uu____10780 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10780 with
            | USolved wl1 ->
                let uu____10782 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10782
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
                  let uu____10834 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10834 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10837 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10849;
                  FStar_Syntax_Syntax.vars = uu____10850;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10853;
                  FStar_Syntax_Syntax.vars = uu____10854;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10866,uu____10867) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10874,FStar_Syntax_Syntax.Tm_uinst uu____10875) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10882 -> USolved wl

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
            ((let uu____10892 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10892
              then
                let uu____10893 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10893 msg
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
        (let uu____10902 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10902
         then
           let uu____10903 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10903
         else ());
        (let uu____10905 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10905 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10971 = head_matches_delta env () t1 t2  in
               match uu____10971 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____11012 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____11061 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____11076 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____11077 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____11076, uu____11077)
                          | FStar_Pervasives_Native.None  ->
                              let uu____11082 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____11083 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____11082, uu____11083)
                           in
                        (match uu____11061 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11113 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_29  ->
                                    FStar_TypeChecker_Common.TProb _0_29)
                                 uu____11113
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11144 =
                                    let uu____11153 =
                                      let uu____11156 =
                                        let uu____11163 =
                                          let uu____11164 =
                                            let uu____11171 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____11171)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11164
                                           in
                                        FStar_Syntax_Syntax.mk uu____11163
                                         in
                                      uu____11156
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____11179 =
                                      let uu____11182 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____11182]  in
                                    (uu____11153, uu____11179)  in
                                  FStar_Pervasives_Native.Some uu____11144
                              | (uu____11195,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11197)) ->
                                  let uu____11202 =
                                    let uu____11209 =
                                      let uu____11212 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____11212]  in
                                    (t11, uu____11209)  in
                                  FStar_Pervasives_Native.Some uu____11202
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11222),uu____11223) ->
                                  let uu____11228 =
                                    let uu____11235 =
                                      let uu____11238 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____11238]  in
                                    (t21, uu____11235)  in
                                  FStar_Pervasives_Native.Some uu____11228
                              | uu____11247 ->
                                  let uu____11252 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____11252 with
                                   | (head1,uu____11276) ->
                                       let uu____11297 =
                                         let uu____11298 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____11298.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____11297 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11309;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11311;_}
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
                                        | uu____11318 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11331) ->
                  let uu____11356 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___111_11382  ->
                            match uu___111_11382 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11389 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____11389 with
                                      | (u',uu____11405) ->
                                          let uu____11426 =
                                            let uu____11427 = whnf env u'  in
                                            uu____11427.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11426 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11431) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11456 -> false))
                                 | uu____11457 -> false)
                            | uu____11460 -> false))
                     in
                  (match uu____11356 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11498 tps =
                         match uu____11498 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11546 =
                                    let uu____11555 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____11555  in
                                  (match uu____11546 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11590 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11599 =
                         let uu____11608 =
                           let uu____11615 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11615, [])  in
                         make_lower_bound uu____11608 lower_bounds  in
                       (match uu____11599 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11627 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11627
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
                            ((let uu____11647 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11647
                              then
                                let wl' =
                                  let uu___140_11649 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___140_11649.wl_deferred);
                                    ctr = (uu___140_11649.ctr);
                                    defer_ok = (uu___140_11649.defer_ok);
                                    smt_ok = (uu___140_11649.smt_ok);
                                    tcenv = (uu___140_11649.tcenv)
                                  }  in
                                let uu____11650 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11650
                              else ());
                             (let uu____11652 =
                                solve_t env eq_prob
                                  (let uu___141_11654 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___141_11654.wl_deferred);
                                     ctr = (uu___141_11654.ctr);
                                     defer_ok = (uu___141_11654.defer_ok);
                                     smt_ok = (uu___141_11654.smt_ok);
                                     tcenv = (uu___141_11654.tcenv)
                                   })
                                 in
                              match uu____11652 with
                              | Success uu____11657 ->
                                  let wl1 =
                                    let uu___142_11659 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___142_11659.wl_deferred);
                                      ctr = (uu___142_11659.ctr);
                                      defer_ok = (uu___142_11659.defer_ok);
                                      smt_ok = (uu___142_11659.smt_ok);
                                      tcenv = (uu___142_11659.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11661 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11666 -> FStar_Pervasives_Native.None))))
              | uu____11667 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11676 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11676
         then
           let uu____11677 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11677
         else ());
        (let uu____11679 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11679 with
         | (u,args) ->
             let uu____11718 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11718 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____11767 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____11767 with
                    | (h1,args1) ->
                        let uu____11808 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11808 with
                         | (h2,uu____11828) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11855 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11855
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11873 =
                                          let uu____11876 =
                                            let uu____11877 =
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
                                                   _0_30) uu____11877
                                             in
                                          [uu____11876]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11873))
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
                                       (let uu____11910 =
                                          let uu____11913 =
                                            let uu____11914 =
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
                                                   _0_31) uu____11914
                                             in
                                          [uu____11913]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11910))
                                  else FStar_Pervasives_Native.None
                              | uu____11928 -> FStar_Pervasives_Native.None))
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
                             let uu____12022 =
                               let uu____12031 =
                                 let uu____12034 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____12034  in
                               (uu____12031, m1)  in
                             FStar_Pervasives_Native.Some uu____12022)
                    | (uu____12047,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12049)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12097),uu____12098) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12145 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12198) ->
                       let uu____12223 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___112_12249  ->
                                 match uu___112_12249 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12256 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____12256 with
                                           | (u',uu____12272) ->
                                               let uu____12293 =
                                                 let uu____12294 =
                                                   whnf env u'  in
                                                 uu____12294.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____12293 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12298) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12323 -> false))
                                      | uu____12324 -> false)
                                 | uu____12327 -> false))
                          in
                       (match uu____12223 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12369 tps =
                              match uu____12369 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12431 =
                                         let uu____12442 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____12442  in
                                       (match uu____12431 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12493 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____12504 =
                              let uu____12515 =
                                let uu____12524 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____12524, [])  in
                              make_upper_bound uu____12515 upper_bounds  in
                            (match uu____12504 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12538 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12538
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
                                 ((let uu____12564 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____12564
                                   then
                                     let wl' =
                                       let uu___143_12566 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___143_12566.wl_deferred);
                                         ctr = (uu___143_12566.ctr);
                                         defer_ok = (uu___143_12566.defer_ok);
                                         smt_ok = (uu___143_12566.smt_ok);
                                         tcenv = (uu___143_12566.tcenv)
                                       }  in
                                     let uu____12567 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12567
                                   else ());
                                  (let uu____12569 =
                                     solve_t env eq_prob
                                       (let uu___144_12571 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___144_12571.wl_deferred);
                                          ctr = (uu___144_12571.ctr);
                                          defer_ok =
                                            (uu___144_12571.defer_ok);
                                          smt_ok = (uu___144_12571.smt_ok);
                                          tcenv = (uu___144_12571.tcenv)
                                        })
                                      in
                                   match uu____12569 with
                                   | Success uu____12574 ->
                                       let wl1 =
                                         let uu___145_12576 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___145_12576.wl_deferred);
                                           ctr = (uu___145_12576.ctr);
                                           defer_ok =
                                             (uu___145_12576.defer_ok);
                                           smt_ok = (uu___145_12576.smt_ok);
                                           tcenv = (uu___145_12576.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____12578 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12583 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12584 -> failwith "Impossible: Not a flex-rigid")))

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
              (let uu____12602 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12602
               then
                 let uu____12603 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12604 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12603 (rel_to_string (p_rel orig)) uu____12604
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____12674 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____12674
                       then
                         let uu____12675 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____12675
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___146_12729 = hd1  in
                       let uu____12730 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___146_12729.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___146_12729.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12730
                       }  in
                     let hd21 =
                       let uu___147_12734 = hd2  in
                       let uu____12735 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___147_12734.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___147_12734.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12735
                       }  in
                     let prob =
                       let uu____12739 =
                         let uu____12744 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____12744 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
                         uu____12739
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____12755 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____12755
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____12759 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____12759 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____12797 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____12802 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____12797 uu____12802
                             in
                          ((let uu____12812 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12812
                            then
                              let uu____12813 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____12814 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____12813 uu____12814
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____12837 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____12847 = aux scope env [] bs1 bs2  in
               match uu____12847 with
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
        (let uu____12872 = compress_tprob wl problem  in
         solve_t' env uu____12872 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12924 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12924 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12955,uu____12956) ->
                    let rec may_relate head3 =
                      let uu____12983 =
                        let uu____12984 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12984.FStar_Syntax_Syntax.n  in
                      match uu____12983 with
                      | FStar_Syntax_Syntax.Tm_name uu____12987 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12988 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13011;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____13012;
                            FStar_Syntax_Syntax.fv_qual = uu____13013;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13016;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13017;
                            FStar_Syntax_Syntax.fv_qual = uu____13018;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13022,uu____13023) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13065) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13071) ->
                          may_relate t
                      | uu____13076 -> false  in
                    let uu____13077 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13077
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
                                 let uu____13098 =
                                   let uu____13099 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13099 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13098
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____13101 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____13101
                    else
                      (let uu____13103 =
                         let uu____13104 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13105 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13104 uu____13105
                          in
                       giveup env1 uu____13103 orig)
                | (uu____13106,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___148_13120 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_13120.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_13120.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___148_13120.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_13120.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_13120.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_13120.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_13120.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_13120.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13121,FStar_Pervasives_Native.None ) ->
                    ((let uu____13133 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13133
                      then
                        let uu____13134 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13135 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13136 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13137 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____13134
                          uu____13135 uu____13136 uu____13137
                      else ());
                     (let uu____13139 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13139 with
                      | (head11,args1) ->
                          let uu____13176 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13176 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____13230 =
                                   let uu____13231 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____13232 = args_to_string args1  in
                                   let uu____13233 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____13234 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____13231 uu____13232 uu____13233
                                     uu____13234
                                    in
                                 giveup env1 uu____13230 orig
                               else
                                 (let uu____13236 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____13242 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____13242 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____13236
                                  then
                                    let uu____13243 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____13243 with
                                    | USolved wl2 ->
                                        let uu____13245 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____13245
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____13249 =
                                       base_and_refinement env1 t1  in
                                     match uu____13249 with
                                     | (base1,refinement1) ->
                                         let uu____13274 =
                                           base_and_refinement env1 t2  in
                                         (match uu____13274 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13331 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13331 with
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
                                                            (fun uu____13353 
                                                               ->
                                                               fun
                                                                 uu____13354 
                                                                 ->
                                                                 match 
                                                                   (uu____13353,
                                                                    uu____13354)
                                                                 with
                                                                 | ((a,uu____13372),
                                                                    (a',uu____13374))
                                                                    ->
                                                                    let uu____13383
                                                                    =
                                                                    let uu____13388
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____13388
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
                                                                    uu____13383)
                                                            args1 args2
                                                           in
                                                        let formula =
                                                          let uu____13394 =
                                                            FStar_List.map
                                                              (fun p  ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____13394
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
                                               | uu____13400 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___149_13436 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___149_13436.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____13473 =
           match uu____13473 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____13517 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____13517 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____13629  ->
                      let uu____13630 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____13630);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____13698  ->
                                match uu____13698 with
                                | (x,imp) ->
                                    let uu____13709 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____13709, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____13722 = FStar_Syntax_Util.type_u ()  in
                        match uu____13722 with
                        | (t1,uu____13728) ->
                            let uu____13729 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____13729
                         in
                      let uu____13734 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____13734 with
                       | (t',tm_u1) ->
                           let uu____13747 = destruct_flex_t t'  in
                           (match uu____13747 with
                            | (uu____13784,u1,k1,uu____13787) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____13846 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13846
                                   in
                                let sol =
                                  let uu____13850 =
                                    let uu____13859 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13859)  in
                                  TERM uu____13850  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____13994  ->
                            let uu____13995 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____13996 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13995 uu____13996);
                       (let uu____14009 = pat_var_opt env pat_args hd1  in
                        match uu____14009 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____14029  ->
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
                                       (fun uu____14072  ->
                                          match uu____14072 with
                                          | (x,uu____14078) ->
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
                                 (fun uu____14093  ->
                                    let uu____14094 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____14107 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____14094
                                      uu____14107);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____14111 =
                                  let uu____14112 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____14112  in
                                if uu____14111
                                then
                                  (debug1
                                     (fun uu____14124  ->
                                        let uu____14125 =
                                          let uu____14128 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____14141 =
                                            let uu____14144 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____14145 =
                                              let uu____14148 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____14149 =
                                                let uu____14152 =
                                                  names_to_string fvs  in
                                                let uu____14153 =
                                                  let uu____14156 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____14156]  in
                                                uu____14152 :: uu____14153
                                                 in
                                              uu____14148 :: uu____14149  in
                                            uu____14144 :: uu____14145  in
                                          uu____14128 :: uu____14141  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____14125);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____14158 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____14161 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____14158 (formal ::
                                     pattern_vars) uu____14161 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____14168::uu____14169) ->
                      let uu____14200 =
                        let uu____14213 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____14213  in
                      (match uu____14200 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____14252 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____14259::uu____14260,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____14283 =
                 let uu____14296 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____14296  in
               (match uu____14283 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____14332  ->
                          let uu____14333 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14334 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14335 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14336 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14333 uu____14334 uu____14335 uu____14336);
                     (let uu____14337 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____14340 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____14337 [] uu____14340 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____14386 = lhs  in
           match uu____14386 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____14396 ->
                     let uu____14397 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____14397 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____14428 = p  in
           match uu____14428 with
           | (((u,k),xs,c),ps,(h,uu____14439,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14527 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____14527 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____14550 = h gs_xs  in
                      let uu____14551 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                         in
                      FStar_Syntax_Util.abs xs1 uu____14550 uu____14551  in
                    ((let uu____14557 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14557
                      then
                        let uu____14558 =
                          let uu____14561 =
                            let uu____14562 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____14562
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____14567 =
                            let uu____14570 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____14571 =
                              let uu____14574 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____14575 =
                                let uu____14578 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____14579 =
                                  let uu____14582 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____14583 =
                                    let uu____14586 =
                                      let uu____14587 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____14587
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____14592 =
                                      let uu____14595 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____14595]  in
                                    uu____14586 :: uu____14592  in
                                  uu____14582 :: uu____14583  in
                                uu____14578 :: uu____14579  in
                              uu____14574 :: uu____14575  in
                            uu____14570 :: uu____14571  in
                          uu____14561 :: uu____14567  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____14558
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___113_14625 =
           match uu___113_14625 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____14667 = p  in
           match uu____14667 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14764 = FStar_List.nth ps i  in
               (match uu____14764 with
                | (pi,uu____14768) ->
                    let uu____14773 = FStar_List.nth xs i  in
                    (match uu____14773 with
                     | (xi,uu____14785) ->
                         let rec gs k =
                           let uu____14800 =
                             let uu____14813 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____14813  in
                           match uu____14800 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____14892)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____14905 = new_uvar r xs k_a  in
                                     (match uu____14905 with
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
                                          let uu____14927 = aux subst2 tl1
                                             in
                                          (match uu____14927 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____14954 =
                                                 let uu____14957 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____14957 :: gi_xs'  in
                                               let uu____14958 =
                                                 let uu____14961 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____14961 :: gi_ps'  in
                                               (uu____14954, uu____14958)))
                                  in
                               aux [] bs
                            in
                         let uu____14966 =
                           let uu____14967 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____14967
                            in
                         if uu____14966
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____14971 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____14971 with
                            | (g_xs,uu____14983) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____14994 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____14995 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_35  ->
                                         FStar_Pervasives_Native.Some _0_35)
                                     in
                                  FStar_Syntax_Util.abs xs uu____14994
                                    uu____14995
                                   in
                                let sub1 =
                                  let uu____15001 =
                                    let uu____15006 = p_scope orig  in
                                    let uu____15007 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____15010 =
                                      let uu____15013 =
                                        FStar_List.map
                                          (fun uu____15028  ->
                                             match uu____15028 with
                                             | (uu____15037,uu____15038,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____15013  in
                                    mk_problem uu____15006 orig uu____15007
                                      (p_rel orig) uu____15010
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_36  ->
                                       FStar_TypeChecker_Common.TProb _0_36)
                                    uu____15001
                                   in
                                ((let uu____15053 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15053
                                  then
                                    let uu____15054 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____15055 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____15054 uu____15055
                                  else ());
                                 (let wl2 =
                                    let uu____15058 =
                                      let uu____15061 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____15061
                                       in
                                    solve_prob orig uu____15058
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____15070 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_37  ->
                                       FStar_Pervasives_Native.Some _0_37)
                                    uu____15070)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____15111 = lhs  in
           match uu____15111 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____15149 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____15149 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____15182 =
                         let uu____15231 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____15231)  in
                       FStar_Pervasives_Native.Some uu____15182
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____15385 =
                            let uu____15392 =
                              let uu____15393 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____15393.FStar_Syntax_Syntax.n  in
                            (uu____15392, args)  in
                          match uu____15385 with
                          | (uu____15404,[]) ->
                              let uu____15407 =
                                let uu____15418 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____15418)  in
                              FStar_Pervasives_Native.Some uu____15407
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____15439,uu____15440) ->
                              let uu____15461 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15461 with
                               | (uv1,uv_args) ->
                                   let uu____15504 =
                                     let uu____15505 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15505.FStar_Syntax_Syntax.n  in
                                   (match uu____15504 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15515) ->
                                        let uu____15540 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15540 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15567  ->
                                                       let uu____15568 =
                                                         let uu____15569 =
                                                           let uu____15570 =
                                                             let uu____15575
                                                               =
                                                               let uu____15576
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15576
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15575
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15570
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15569
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15568))
                                                in
                                             let c1 =
                                               let uu____15586 =
                                                 let uu____15587 =
                                                   let uu____15592 =
                                                     let uu____15593 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15593
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15592
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15587
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15586
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15606 =
                                                 let uu____15609 =
                                                   let uu____15610 =
                                                     let uu____15613 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15613
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15610
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15609
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15606
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15632 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____15637,uu____15638) ->
                              let uu____15657 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____15657 with
                               | (uv1,uv_args) ->
                                   let uu____15700 =
                                     let uu____15701 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____15701.FStar_Syntax_Syntax.n  in
                                   (match uu____15700 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____15711) ->
                                        let uu____15736 =
                                          pat_vars env [] uv_args  in
                                        (match uu____15736 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15763  ->
                                                       let uu____15764 =
                                                         let uu____15765 =
                                                           let uu____15766 =
                                                             let uu____15771
                                                               =
                                                               let uu____15772
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15772
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15771
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15766
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15765
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15764))
                                                in
                                             let c1 =
                                               let uu____15782 =
                                                 let uu____15783 =
                                                   let uu____15788 =
                                                     let uu____15789 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15789
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15788
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15783
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15782
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15802 =
                                                 let uu____15805 =
                                                   let uu____15806 =
                                                     let uu____15809 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15809
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15806
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15805
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15802
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15828 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____15835) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____15876 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____15876
                                  (fun _0_38  ->
                                     FStar_Pervasives_Native.Some _0_38)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____15912 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____15912 with
                                   | (args1,rest) ->
                                       let uu____15941 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____15941 with
                                        | (xs2,c2) ->
                                            let uu____15954 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____15954
                                              (fun uu____15978  ->
                                                 match uu____15978 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____16018 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____16018 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16086 =
                                         let uu____16091 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____16091
                                          in
                                       FStar_All.pipe_right uu____16086
                                         (fun _0_39  ->
                                            FStar_Pervasives_Native.Some
                                              _0_39))
                          | uu____16106 ->
                              let uu____16113 =
                                let uu____16118 =
                                  let uu____16119 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____16120 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____16121 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____16119 uu____16120 uu____16121
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____16118)
                                 in
                              FStar_Errors.raise_error uu____16113
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____16128 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____16128
                          (fun uu____16185  ->
                             match uu____16185 with
                             | (xs1,c1) ->
                                 let uu____16236 =
                                   let uu____16279 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____16279)
                                    in
                                 FStar_Pervasives_Native.Some uu____16236))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____16416 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____16436 = project orig env wl1 i st  in
                      match uu____16436 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____16450) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____16465 = imitate orig env wl1 st  in
                   match uu____16465 with
                   | Failed uu____16470 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____16509 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____16509 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____16532 = forced_lhs_pattern  in
                     (match uu____16532 with
                      | (lhs_t,uu____16534,uu____16535,uu____16536) ->
                          ((let uu____16538 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16538
                            then
                              let uu____16539 = lhs1  in
                              match uu____16539 with
                              | (t0,uu____16541,uu____16542,uu____16543) ->
                                  let uu____16544 = forced_lhs_pattern  in
                                  (match uu____16544 with
                                   | (t11,uu____16546,uu____16547,uu____16548)
                                       ->
                                       let uu____16549 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____16550 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____16549 uu____16550)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____16558 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____16558
                            then
                              ((let uu____16560 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16560
                                then
                                  let uu____16561 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____16562 = names_to_string rhs_vars
                                     in
                                  let uu____16563 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____16561 uu____16562 uu____16563
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____16567 =
                                  let uu____16568 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____16568 wl2  in
                                match uu____16567 with
                                | Failed uu____16569 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____16578 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____16578
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____16595 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____16595 with
                 | (hd1,uu____16611) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____16632 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____16645 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____16646 -> true
                      | uu____16663 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____16667 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____16667
                          then true
                          else
                            ((let uu____16670 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____16670
                              then
                                let uu____16671 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____16671
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
                    let uu____16691 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____16691 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____16704 =
                             let uu____16705 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____16705
                              in
                           giveup_or_defer1 orig uu____16704
                         else
                           (let uu____16707 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____16707
                            then
                              let uu____16708 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____16708
                               then
                                 let uu____16709 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____16709
                               else
                                 ((let uu____16714 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____16714
                                   then
                                     let uu____16715 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____16716 = names_to_string fvs1
                                        in
                                     let uu____16717 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____16715 uu____16716 uu____16717
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
                                (let uu____16721 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____16721
                                 then
                                   ((let uu____16723 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____16723
                                     then
                                       let uu____16724 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____16725 = names_to_string fvs1
                                          in
                                       let uu____16726 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____16724 uu____16725 uu____16726
                                     else ());
                                    (let uu____16728 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____16728))
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
                      (let uu____16739 =
                         let uu____16740 = FStar_Syntax_Free.names t1  in
                         check_head uu____16740 t2  in
                       if uu____16739
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____16751 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16751
                           then
                             let uu____16752 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____16753 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____16752 uu____16753
                           else ());
                          (let uu____16761 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____16761))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____16852 uu____16853 r =
                match (uu____16852, uu____16853) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____17051 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____17051
                    then
                      let uu____17052 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____17052
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____17076 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____17076
                        then
                          let uu____17077 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____17078 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____17079 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____17080 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____17081 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____17077 uu____17078 uu____17079 uu____17080
                            uu____17081
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____17147 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____17147 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____17161 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____17161 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____17215 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____17215
                                      in
                                   let uu____17218 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____17218 k3)
                            else
                              (let uu____17222 =
                                 let uu____17223 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____17224 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____17225 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____17223 uu____17224 uu____17225
                                  in
                               failwith uu____17222)
                           in
                        let uu____17226 =
                          let uu____17233 =
                            let uu____17246 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____17246  in
                          match uu____17233 with
                          | (bs,k1') ->
                              let uu____17271 =
                                let uu____17284 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____17284
                                 in
                              (match uu____17271 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____17312 =
                                       let uu____17317 = p_scope orig  in
                                       mk_problem uu____17317 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_40  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_40) uu____17312
                                      in
                                   let uu____17322 =
                                     let uu____17327 =
                                       let uu____17328 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____17328.FStar_Syntax_Syntax.n  in
                                     let uu____17331 =
                                       let uu____17332 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____17332.FStar_Syntax_Syntax.n  in
                                     (uu____17327, uu____17331)  in
                                   (match uu____17322 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____17341,uu____17342) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____17345,FStar_Syntax_Syntax.Tm_type
                                       uu____17346) -> (k2'_ys, [sub_prob])
                                    | uu____17349 ->
                                        let uu____17354 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____17354 with
                                         | (t,uu____17366) ->
                                             let uu____17367 =
                                               new_uvar r zs t  in
                                             (match uu____17367 with
                                              | (k_zs,uu____17379) ->
                                                  let kprob =
                                                    let uu____17381 =
                                                      let uu____17386 =
                                                        p_scope orig  in
                                                      mk_problem uu____17386
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_41  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_41) uu____17381
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____17226 with
                        | (k_u',sub_probs) ->
                            let uu____17399 =
                              let uu____17410 =
                                let uu____17411 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____17411
                                 in
                              let uu____17420 =
                                let uu____17423 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____17423  in
                              let uu____17426 =
                                let uu____17429 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____17429  in
                              (uu____17410, uu____17420, uu____17426)  in
                            (match uu____17399 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____17448 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____17448 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____17467 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____17467
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
                                            let uu____17471 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____17471 with
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
              let solve_one_pat uu____17528 uu____17529 =
                match (uu____17528, uu____17529) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____17647 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____17647
                      then
                        let uu____17648 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____17649 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____17648 uu____17649
                      else ());
                     (let uu____17651 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____17651
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____17670  ->
                               fun uu____17671  ->
                                 match (uu____17670, uu____17671) with
                                 | ((a,uu____17689),(t21,uu____17691)) ->
                                     let uu____17700 =
                                       let uu____17705 = p_scope orig  in
                                       let uu____17706 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____17705 orig
                                         uu____17706
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____17700
                                       (fun _0_42  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_42)) xs args2
                           in
                        let guard =
                          let uu____17712 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____17712  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____17727 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____17727 with
                         | (occurs_ok,uu____17735) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____17743 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____17743
                             then
                               let sol =
                                 let uu____17745 =
                                   let uu____17754 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____17754)  in
                                 TERM uu____17745  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____17761 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____17761
                                then
                                  let uu____17762 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____17762 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____17786,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____17812 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____17812
                                        then
                                          let uu____17813 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____17813
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____17820 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____17822 = lhs  in
              match uu____17822 with
              | (t1,u1,k1,args1) ->
                  let uu____17827 = rhs  in
                  (match uu____17827 with
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
                        | uu____17867 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____17877 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____17877 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____17895) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____17902 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____17902
                                     then
                                       let uu____17903 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____17903
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____17910 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17913 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17913
          then
            let uu____17914 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17914
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____17918 = FStar_Util.physical_equality t1 t2  in
             if uu____17918
             then
               let uu____17919 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____17919
             else
               ((let uu____17922 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____17922
                 then
                   let uu____17923 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____17924 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____17925 = FStar_Syntax_Print.tag_of_term t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17923
                     uu____17924 uu____17925
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____17928,uu____17929)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____17954,FStar_Syntax_Syntax.Tm_delayed uu____17955)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____17980,uu____17981)
                     ->
                     let uu____18008 =
                       let uu___150_18009 = problem  in
                       let uu____18010 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_18009.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18010;
                         FStar_TypeChecker_Common.relation =
                           (uu___150_18009.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___150_18009.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___150_18009.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_18009.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_18009.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_18009.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_18009.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_18009.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18008 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____18011,uu____18012) ->
                     let uu____18019 =
                       let uu___151_18020 = problem  in
                       let uu____18021 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_18020.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18021;
                         FStar_TypeChecker_Common.relation =
                           (uu___151_18020.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___151_18020.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___151_18020.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_18020.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_18020.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_18020.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_18020.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_18020.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18019 wl
                 | (uu____18022,FStar_Syntax_Syntax.Tm_ascribed uu____18023)
                     ->
                     let uu____18050 =
                       let uu___152_18051 = problem  in
                       let uu____18052 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_18051.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___152_18051.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___152_18051.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18052;
                         FStar_TypeChecker_Common.element =
                           (uu___152_18051.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_18051.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___152_18051.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_18051.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_18051.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_18051.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18050 wl
                 | (uu____18053,FStar_Syntax_Syntax.Tm_meta uu____18054) ->
                     let uu____18061 =
                       let uu___153_18062 = problem  in
                       let uu____18063 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___153_18062.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___153_18062.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___153_18062.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18063;
                         FStar_TypeChecker_Common.element =
                           (uu___153_18062.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___153_18062.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___153_18062.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___153_18062.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___153_18062.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___153_18062.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____18061 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____18065),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____18067)) ->
                     let uu____18076 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____18076
                 | (FStar_Syntax_Syntax.Tm_bvar uu____18077,uu____18078) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____18079,FStar_Syntax_Syntax.Tm_bvar uu____18080) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___114_18139 =
                       match uu___114_18139 with
                       | [] -> c
                       | bs ->
                           let uu____18161 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____18161
                        in
                     let uu____18170 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____18170 with
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
                                     let uu____18314 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____18314
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____18316 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_43  ->
                                        FStar_TypeChecker_Common.CProb _0_43)
                                     uu____18316))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___115_18398 =
                       match uu___115_18398 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18432 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____18432 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____18570 =
                                     let uu____18575 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____18576 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____18575
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____18576
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_44  ->
                                        FStar_TypeChecker_Common.TProb _0_44)
                                     uu____18570))
                 | (FStar_Syntax_Syntax.Tm_abs uu____18581,uu____18582) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18609 -> true
                       | uu____18626 -> false  in
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
                         (let uu____18677 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_18685 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_18685.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_18685.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_18685.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_18685.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_18685.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_18685.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_18685.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_18685.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_18685.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_18685.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_18685.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_18685.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_18685.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_18685.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_18685.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_18685.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_18685.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_18685.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_18685.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_18685.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_18685.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_18685.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_18685.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_18685.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_18685.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_18685.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_18685.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_18685.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_18685.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_18685.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_18685.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_18685.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_18685.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_18685.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18677 with
                          | (uu____18688,ty,uu____18690) ->
                              let uu____18691 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18691)
                        in
                     let uu____18692 =
                       let uu____18709 = maybe_eta t1  in
                       let uu____18716 = maybe_eta t2  in
                       (uu____18709, uu____18716)  in
                     (match uu____18692 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_18758 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18758.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_18758.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18758.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18758.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18758.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18758.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18758.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18758.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18781 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18781
                          then
                            let uu____18782 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18782 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18797 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18797.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18797.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18797.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18797.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18797.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18797.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18797.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18797.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18821 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18821
                          then
                            let uu____18822 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18822 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18837 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18837.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18837.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18837.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18837.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18837.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18837.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18837.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18837.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18841 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____18858,FStar_Syntax_Syntax.Tm_abs uu____18859) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18886 -> true
                       | uu____18903 -> false  in
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
                         (let uu____18954 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_18962 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_18962.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_18962.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_18962.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_18962.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_18962.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_18962.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_18962.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_18962.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_18962.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_18962.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_18962.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_18962.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_18962.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_18962.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_18962.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_18962.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_18962.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_18962.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_18962.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_18962.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_18962.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_18962.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_18962.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_18962.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_18962.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_18962.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_18962.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_18962.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_18962.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_18962.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_18962.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_18962.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_18962.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_18962.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18954 with
                          | (uu____18965,ty,uu____18967) ->
                              let uu____18968 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18968)
                        in
                     let uu____18969 =
                       let uu____18986 = maybe_eta t1  in
                       let uu____18993 = maybe_eta t2  in
                       (uu____18986, uu____18993)  in
                     (match uu____18969 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_19035 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_19035.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_19035.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_19035.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_19035.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_19035.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_19035.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_19035.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_19035.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____19058 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19058
                          then
                            let uu____19059 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19059 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19074 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19074.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19074.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19074.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19074.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19074.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19074.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19074.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19074.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____19098 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____19098
                          then
                            let uu____19099 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____19099 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_19114 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_19114.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_19114.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_19114.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_19114.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_19114.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_19114.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_19114.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_19114.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____19118 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____19150 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____19150) &&
                          (let uu____19162 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____19162))
                         &&
                         (let uu____19177 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____19177 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___116_19189 =
                                match uu___116_19189 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____19190 -> true
                                | uu____19191 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____19192 -> false)
                        in
                     let uu____19193 = as_refinement should_delta env wl t1
                        in
                     (match uu____19193 with
                      | (x11,phi1) ->
                          let uu____19200 =
                            as_refinement should_delta env wl t2  in
                          (match uu____19200 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____19208 =
                                   let uu____19213 = p_scope orig  in
                                   mk_problem uu____19213 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_45  ->
                                      FStar_TypeChecker_Common.TProb _0_45)
                                   uu____19208
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
                                 let uu____19253 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____19253
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____19259 =
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
                                   let uu____19265 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19265 impl
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
                                   let uu____19274 =
                                     let uu____19279 =
                                       let uu____19280 = p_scope orig  in
                                       let uu____19287 =
                                         let uu____19294 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____19294]  in
                                       FStar_List.append uu____19280
                                         uu____19287
                                        in
                                     mk_problem uu____19279 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_46  ->
                                        FStar_TypeChecker_Common.TProb _0_46)
                                     uu____19274
                                    in
                                 let uu____19303 =
                                   solve env1
                                     (let uu___157_19305 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___157_19305.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___157_19305.smt_ok);
                                        tcenv = (uu___157_19305.tcenv)
                                      })
                                    in
                                 (match uu____19303 with
                                  | Failed uu____19312 -> fallback ()
                                  | Success uu____19317 ->
                                      let guard =
                                        let uu____19321 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____19326 =
                                          let uu____19327 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____19327
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____19321
                                          uu____19326
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___158_19336 = wl1  in
                                        {
                                          attempting =
                                            (uu___158_19336.attempting);
                                          wl_deferred =
                                            (uu___158_19336.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___158_19336.defer_ok);
                                          smt_ok = (uu___158_19336.smt_ok);
                                          tcenv = (uu___158_19336.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19338,FStar_Syntax_Syntax.Tm_uvar uu____19339) ->
                     let uu____19372 = destruct_flex_t t1  in
                     let uu____19373 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19372 uu____19373
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19374;
                       FStar_Syntax_Syntax.pos = uu____19375;
                       FStar_Syntax_Syntax.vars = uu____19376;_},uu____19377),FStar_Syntax_Syntax.Tm_uvar
                    uu____19378) ->
                     let uu____19431 = destruct_flex_t t1  in
                     let uu____19432 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19431 uu____19432
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19433,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19434;
                       FStar_Syntax_Syntax.pos = uu____19435;
                       FStar_Syntax_Syntax.vars = uu____19436;_},uu____19437))
                     ->
                     let uu____19490 = destruct_flex_t t1  in
                     let uu____19491 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19490 uu____19491
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19492;
                       FStar_Syntax_Syntax.pos = uu____19493;
                       FStar_Syntax_Syntax.vars = uu____19494;_},uu____19495),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19496;
                       FStar_Syntax_Syntax.pos = uu____19497;
                       FStar_Syntax_Syntax.vars = uu____19498;_},uu____19499))
                     ->
                     let uu____19572 = destruct_flex_t t1  in
                     let uu____19573 = destruct_flex_t t2  in
                     flex_flex1 orig uu____19572 uu____19573
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19574,uu____19575) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19592 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19592 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19599;
                       FStar_Syntax_Syntax.pos = uu____19600;
                       FStar_Syntax_Syntax.vars = uu____19601;_},uu____19602),uu____19603)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____19640 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____19640 t2 wl
                 | (uu____19647,FStar_Syntax_Syntax.Tm_uvar uu____19648) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____19665,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19666;
                       FStar_Syntax_Syntax.pos = uu____19667;
                       FStar_Syntax_Syntax.vars = uu____19668;_},uu____19669))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19706,FStar_Syntax_Syntax.Tm_type uu____19707) ->
                     solve_t' env
                       (let uu___159_19725 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19725.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19725.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19725.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19725.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19725.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19725.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19725.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19725.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19725.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19726;
                       FStar_Syntax_Syntax.pos = uu____19727;
                       FStar_Syntax_Syntax.vars = uu____19728;_},uu____19729),FStar_Syntax_Syntax.Tm_type
                    uu____19730) ->
                     solve_t' env
                       (let uu___159_19768 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19768.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19768.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19768.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19768.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19768.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19768.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19768.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19768.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19768.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____19769,FStar_Syntax_Syntax.Tm_arrow uu____19770) ->
                     solve_t' env
                       (let uu___159_19800 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19800.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19800.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19800.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19800.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19800.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19800.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19800.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19800.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19800.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19801;
                       FStar_Syntax_Syntax.pos = uu____19802;
                       FStar_Syntax_Syntax.vars = uu____19803;_},uu____19804),FStar_Syntax_Syntax.Tm_arrow
                    uu____19805) ->
                     solve_t' env
                       (let uu___159_19855 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_19855.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_19855.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_19855.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_19855.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_19855.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_19855.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_19855.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_19855.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_19855.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19856,uu____19857) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19876 =
                          let uu____19877 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19877
                           in
                        if uu____19876
                        then
                          let uu____19878 =
                            FStar_All.pipe_left
                              (fun _0_47  ->
                                 FStar_TypeChecker_Common.TProb _0_47)
                              (let uu___160_19884 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_19884.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_19884.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_19884.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_19884.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_19884.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_19884.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_19884.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_19884.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_19884.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19885 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19878 uu____19885 t2
                            wl
                        else
                          (let uu____19893 = base_and_refinement env t2  in
                           match uu____19893 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19922 =
                                      FStar_All.pipe_left
                                        (fun _0_48  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_48)
                                        (let uu___161_19928 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_19928.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_19928.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_19928.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_19928.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_19928.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_19928.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_19928.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_19928.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_19928.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19929 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19922
                                      uu____19929 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_19943 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_19943.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_19943.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19946 =
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
                                             _0_49) uu____19946
                                       in
                                    let guard =
                                      let uu____19958 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19958
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
                         uu____19966;
                       FStar_Syntax_Syntax.pos = uu____19967;
                       FStar_Syntax_Syntax.vars = uu____19968;_},uu____19969),uu____19970)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____20009 =
                          let uu____20010 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____20010
                           in
                        if uu____20009
                        then
                          let uu____20011 =
                            FStar_All.pipe_left
                              (fun _0_50  ->
                                 FStar_TypeChecker_Common.TProb _0_50)
                              (let uu___160_20017 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_20017.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_20017.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_20017.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_20017.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_20017.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_20017.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_20017.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_20017.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_20017.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____20018 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____20011 uu____20018 t2
                            wl
                        else
                          (let uu____20026 = base_and_refinement env t2  in
                           match uu____20026 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20055 =
                                      FStar_All.pipe_left
                                        (fun _0_51  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_51)
                                        (let uu___161_20061 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_20061.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_20061.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_20061.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_20061.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_20061.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_20061.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_20061.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_20061.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_20061.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____20062 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____20055
                                      uu____20062 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_20076 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_20076.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_20076.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____20079 =
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
                                             _0_52) uu____20079
                                       in
                                    let guard =
                                      let uu____20091 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____20091
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____20099,FStar_Syntax_Syntax.Tm_uvar uu____20100) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20118 = base_and_refinement env t1  in
                        match uu____20118 with
                        | (t_base,uu____20130) ->
                            solve_t env
                              (let uu___163_20144 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20144.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20144.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20144.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20144.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20144.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20144.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20144.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20144.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____20145,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____20146;
                       FStar_Syntax_Syntax.pos = uu____20147;
                       FStar_Syntax_Syntax.vars = uu____20148;_},uu____20149))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____20187 = base_and_refinement env t1  in
                        match uu____20187 with
                        | (t_base,uu____20199) ->
                            solve_t env
                              (let uu___163_20213 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_20213.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_20213.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_20213.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_20213.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_20213.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_20213.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_20213.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_20213.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____20214,uu____20215) ->
                     let t21 =
                       let uu____20225 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____20225  in
                     solve_t env
                       (let uu___164_20249 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___164_20249.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___164_20249.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___164_20249.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___164_20249.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___164_20249.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___164_20249.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___164_20249.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___164_20249.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___164_20249.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____20250,FStar_Syntax_Syntax.Tm_refine uu____20251) ->
                     let t11 =
                       let uu____20261 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____20261  in
                     solve_t env
                       (let uu___165_20285 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_20285.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_20285.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_20285.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_20285.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_20285.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_20285.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_20285.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_20285.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_20285.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                     let sc_prob =
                       let uu____20365 =
                         let uu____20370 = p_scope orig  in
                         mk_problem uu____20370 orig t11
                           FStar_TypeChecker_Common.EQ t21
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_TypeChecker_Common.TProb _0_53)
                         uu____20365
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____20560 = br1  in
                           (match uu____20560 with
                            | (p1,w1,uu____20579) ->
                                let uu____20592 = br2  in
                                (match uu____20592 with
                                 | (p2,w2,uu____20607) ->
                                     let uu____20612 =
                                       let uu____20613 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____20613  in
                                     if uu____20612
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____20621 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____20621 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____20664 = br2  in
                                            (match uu____20664 with
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
                                                   let uu____20695 =
                                                     p_scope orig  in
                                                   let uu____20702 =
                                                     let uu____20709 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____20709
                                                      in
                                                   FStar_List.append
                                                     uu____20695 uu____20702
                                                    in
                                                 let uu____20720 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____20735,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____20748) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____20781 =
                                                         let uu____20784 =
                                                           let uu____20785 =
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
                                                             uu____20785
                                                            in
                                                         [uu____20784]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20781
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____20720
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____20809 =
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
                                                          uu____20809
                                                         in
                                                      let uu____20820 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____20820
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____20881 -> FStar_Pervasives_Native.None  in
                     let uu____20912 = solve_branches brs1 brs2  in
                     (match uu____20912 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let wl1 =
                            solve_prob orig FStar_Pervasives_Native.None []
                              wl
                             in
                          solve env (attempt sub_probs1 wl1))
                 | (FStar_Syntax_Syntax.Tm_match uu____20928,uu____20929) ->
                     let head1 =
                       let uu____20955 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20955
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20999 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20999
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21041 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21041
                       then
                         let uu____21042 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21043 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21044 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21042 uu____21043 uu____21044
                       else ());
                      (let uu____21046 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21046
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21061 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21061
                          then
                            let guard =
                              let uu____21073 =
                                let uu____21074 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21074 = FStar_Syntax_Util.Equal  in
                              if uu____21073
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21078 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   uu____21078)
                               in
                            let uu____21081 = solve_prob orig guard [] wl  in
                            solve env uu____21081
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____21084,uu____21085) ->
                     let head1 =
                       let uu____21095 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21095
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21139 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21139
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21181 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21181
                       then
                         let uu____21182 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21183 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21184 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21182 uu____21183 uu____21184
                       else ());
                      (let uu____21186 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21186
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21201 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21201
                          then
                            let guard =
                              let uu____21213 =
                                let uu____21214 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21214 = FStar_Syntax_Util.Equal  in
                              if uu____21213
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21218 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   uu____21218)
                               in
                            let uu____21221 = solve_prob orig guard [] wl  in
                            solve env uu____21221
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____21224,uu____21225) ->
                     let head1 =
                       let uu____21229 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21229
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21273 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21273
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21315 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21315
                       then
                         let uu____21316 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21317 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21318 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21316 uu____21317 uu____21318
                       else ());
                      (let uu____21320 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21320
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21335 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21335
                          then
                            let guard =
                              let uu____21347 =
                                let uu____21348 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21348 = FStar_Syntax_Util.Equal  in
                              if uu____21347
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21352 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_Pervasives_Native.Some _0_58)
                                   uu____21352)
                               in
                            let uu____21355 = solve_prob orig guard [] wl  in
                            solve env uu____21355
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____21358,uu____21359)
                     ->
                     let head1 =
                       let uu____21363 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21363
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21407 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21407
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21449 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21449
                       then
                         let uu____21450 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21451 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21452 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21450 uu____21451 uu____21452
                       else ());
                      (let uu____21454 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21454
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21469 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21469
                          then
                            let guard =
                              let uu____21481 =
                                let uu____21482 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21482 = FStar_Syntax_Util.Equal  in
                              if uu____21481
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21486 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_Pervasives_Native.Some _0_59)
                                   uu____21486)
                               in
                            let uu____21489 = solve_prob orig guard [] wl  in
                            solve env uu____21489
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____21492,uu____21493) ->
                     let head1 =
                       let uu____21497 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21497
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21541 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21541
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21583 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21583
                       then
                         let uu____21584 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21585 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21586 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21584 uu____21585 uu____21586
                       else ());
                      (let uu____21588 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21588
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21603 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21603
                          then
                            let guard =
                              let uu____21615 =
                                let uu____21616 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21616 = FStar_Syntax_Util.Equal  in
                              if uu____21615
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21620 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____21620)
                               in
                            let uu____21623 = solve_prob orig guard [] wl  in
                            solve env uu____21623
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____21626,uu____21627) ->
                     let head1 =
                       let uu____21645 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21645
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21689 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21689
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21731 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21731
                       then
                         let uu____21732 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21733 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21734 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21732 uu____21733 uu____21734
                       else ());
                      (let uu____21736 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21736
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21751 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21751
                          then
                            let guard =
                              let uu____21763 =
                                let uu____21764 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21764 = FStar_Syntax_Util.Equal  in
                              if uu____21763
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21768 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____21768)
                               in
                            let uu____21771 = solve_prob orig guard [] wl  in
                            solve env uu____21771
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21774,FStar_Syntax_Syntax.Tm_match uu____21775) ->
                     let head1 =
                       let uu____21801 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21801
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21845 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21845
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21887 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21887
                       then
                         let uu____21888 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21889 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21890 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21888 uu____21889 uu____21890
                       else ());
                      (let uu____21892 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21892
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21907 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21907
                          then
                            let guard =
                              let uu____21919 =
                                let uu____21920 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21920 = FStar_Syntax_Util.Equal  in
                              if uu____21919
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21924 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____21924)
                               in
                            let uu____21927 = solve_prob orig guard [] wl  in
                            solve env uu____21927
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21930,FStar_Syntax_Syntax.Tm_uinst uu____21931) ->
                     let head1 =
                       let uu____21941 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21941
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21985 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21985
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22027 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22027
                       then
                         let uu____22028 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22029 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22030 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22028 uu____22029 uu____22030
                       else ());
                      (let uu____22032 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22032
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22047 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22047
                          then
                            let guard =
                              let uu____22059 =
                                let uu____22060 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22060 = FStar_Syntax_Util.Equal  in
                              if uu____22059
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22064 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   uu____22064)
                               in
                            let uu____22067 = solve_prob orig guard [] wl  in
                            solve env uu____22067
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22070,FStar_Syntax_Syntax.Tm_name uu____22071) ->
                     let head1 =
                       let uu____22075 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22075
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22119 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22119
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22161 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22161
                       then
                         let uu____22162 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22163 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22164 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22162 uu____22163 uu____22164
                       else ());
                      (let uu____22166 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22166
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22181 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22181
                          then
                            let guard =
                              let uu____22193 =
                                let uu____22194 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22194 = FStar_Syntax_Util.Equal  in
                              if uu____22193
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22198 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   uu____22198)
                               in
                            let uu____22201 = solve_prob orig guard [] wl  in
                            solve env uu____22201
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22204,FStar_Syntax_Syntax.Tm_constant uu____22205)
                     ->
                     let head1 =
                       let uu____22209 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22209
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22253 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22253
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22295 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22295
                       then
                         let uu____22296 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22297 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22298 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22296 uu____22297 uu____22298
                       else ());
                      (let uu____22300 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22300
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22315 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22315
                          then
                            let guard =
                              let uu____22327 =
                                let uu____22328 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22328 = FStar_Syntax_Util.Equal  in
                              if uu____22327
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22332 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   uu____22332)
                               in
                            let uu____22335 = solve_prob orig guard [] wl  in
                            solve env uu____22335
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22338,FStar_Syntax_Syntax.Tm_fvar uu____22339) ->
                     let head1 =
                       let uu____22343 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22343
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22387 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22387
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22429 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22429
                       then
                         let uu____22430 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22431 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22432 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22430 uu____22431 uu____22432
                       else ());
                      (let uu____22434 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22434
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22449 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22449
                          then
                            let guard =
                              let uu____22461 =
                                let uu____22462 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22462 = FStar_Syntax_Util.Equal  in
                              if uu____22461
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22466 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   uu____22466)
                               in
                            let uu____22469 = solve_prob orig guard [] wl  in
                            solve env uu____22469
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____22472,FStar_Syntax_Syntax.Tm_app uu____22473) ->
                     let head1 =
                       let uu____22491 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____22491
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____22535 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____22535
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____22577 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____22577
                       then
                         let uu____22578 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____22579 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____22580 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____22578 uu____22579 uu____22580
                       else ());
                      (let uu____22582 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22582
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____22597 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____22597
                          then
                            let guard =
                              let uu____22609 =
                                let uu____22610 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____22610 = FStar_Syntax_Util.Equal  in
                              if uu____22609
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____22614 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   uu____22614)
                               in
                            let uu____22617 = solve_prob orig guard [] wl  in
                            solve env uu____22617
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____22620,FStar_Syntax_Syntax.Tm_let uu____22621) ->
                     let uu____22646 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____22646
                     then
                       let uu____22647 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____22647
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____22649,uu____22650) ->
                     let uu____22663 =
                       let uu____22668 =
                         let uu____22669 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22670 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22671 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22672 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22669 uu____22670 uu____22671 uu____22672
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22668)
                        in
                     FStar_Errors.raise_error uu____22663
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____22673,FStar_Syntax_Syntax.Tm_let uu____22674) ->
                     let uu____22687 =
                       let uu____22692 =
                         let uu____22693 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____22694 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____22695 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____22696 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____22693 uu____22694 uu____22695 uu____22696
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____22692)
                        in
                     FStar_Errors.raise_error uu____22687
                       t1.FStar_Syntax_Syntax.pos
                 | uu____22697 -> giveup env "head tag mismatch" orig)))))

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
          let uu____22733 = p_scope orig  in
          mk_problem uu____22733 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____22746 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____22746
           then
             let uu____22747 =
               let uu____22748 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____22748  in
             let uu____22749 =
               let uu____22750 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____22750  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____22747 uu____22749
           else ());
          (let uu____22752 =
             let uu____22753 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____22753  in
           if uu____22752
           then
             let uu____22754 =
               let uu____22755 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____22756 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____22755 uu____22756
                in
             giveup env uu____22754 orig
           else
             (let ret_sub_prob =
                let uu____22759 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                  uu____22759
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____22786  ->
                     fun uu____22787  ->
                       match (uu____22786, uu____22787) with
                       | ((a1,uu____22805),(a2,uu____22807)) ->
                           let uu____22816 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_69  ->
                                FStar_TypeChecker_Common.TProb _0_69)
                             uu____22816)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____22829 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____22829  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22861 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22868)::[] -> wp1
              | uu____22885 ->
                  let uu____22894 =
                    let uu____22895 =
                      let uu____22896 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____22896  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22895
                     in
                  failwith uu____22894
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____22904 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____22904]
              | x -> x  in
            let uu____22906 =
              let uu____22915 =
                let uu____22916 =
                  let uu____22917 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____22917 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____22916  in
              [uu____22915]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22906;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22918 = lift_c1 ()  in solve_eq uu____22918 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_22924  ->
                       match uu___117_22924 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22925 -> false))
                in
             let uu____22926 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____22960)::uu____22961,(wp2,uu____22963)::uu____22964)
                   -> (wp1, wp2)
               | uu____23021 ->
                   let uu____23042 =
                     let uu____23047 =
                       let uu____23048 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23049 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23048 uu____23049
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23047)
                      in
                   FStar_Errors.raise_error uu____23042
                     env.FStar_TypeChecker_Env.range
                in
             match uu____22926 with
             | (wpc1,wpc2) ->
                 let uu____23068 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23068
                 then
                   let uu____23071 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23071 wl
                 else
                   (let uu____23075 =
                      let uu____23082 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23082  in
                    match uu____23075 with
                    | (c2_decl,qualifiers) ->
                        let uu____23103 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23103
                        then
                          let c1_repr =
                            let uu____23107 =
                              let uu____23108 =
                                let uu____23109 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____23109  in
                              let uu____23110 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23108 uu____23110
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23107
                             in
                          let c2_repr =
                            let uu____23112 =
                              let uu____23113 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____23114 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23113 uu____23114
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____23112
                             in
                          let prob =
                            let uu____23116 =
                              let uu____23121 =
                                let uu____23122 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____23123 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23122
                                  uu____23123
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23121
                               in
                            FStar_TypeChecker_Common.TProb uu____23116  in
                          let wl1 =
                            let uu____23125 =
                              let uu____23128 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____23128  in
                            solve_prob orig uu____23125 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23137 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23137
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____23140 =
                                     let uu____23147 =
                                       let uu____23148 =
                                         let uu____23163 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____23164 =
                                           let uu____23167 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____23168 =
                                             let uu____23171 =
                                               let uu____23172 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23172
                                                in
                                             [uu____23171]  in
                                           uu____23167 :: uu____23168  in
                                         (uu____23163, uu____23164)  in
                                       FStar_Syntax_Syntax.Tm_app uu____23148
                                        in
                                     FStar_Syntax_Syntax.mk uu____23147  in
                                   uu____23140 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____23181 =
                                    let uu____23188 =
                                      let uu____23189 =
                                        let uu____23204 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____23205 =
                                          let uu____23208 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____23209 =
                                            let uu____23212 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____23213 =
                                              let uu____23216 =
                                                let uu____23217 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23217
                                                 in
                                              [uu____23216]  in
                                            uu____23212 :: uu____23213  in
                                          uu____23208 :: uu____23209  in
                                        (uu____23204, uu____23205)  in
                                      FStar_Syntax_Syntax.Tm_app uu____23189
                                       in
                                    FStar_Syntax_Syntax.mk uu____23188  in
                                  uu____23181 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23224 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____23224
                              in
                           let wl1 =
                             let uu____23234 =
                               let uu____23237 =
                                 let uu____23240 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23240 g  in
                               FStar_All.pipe_left
                                 (fun _0_71  ->
                                    FStar_Pervasives_Native.Some _0_71)
                                 uu____23237
                                in
                             solve_prob orig uu____23234 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23253 = FStar_Util.physical_equality c1 c2  in
        if uu____23253
        then
          let uu____23254 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23254
        else
          ((let uu____23257 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23257
            then
              let uu____23258 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____23259 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23258
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23259
            else ());
           (let uu____23261 =
              let uu____23266 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____23267 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____23266, uu____23267)  in
            match uu____23261 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23271),FStar_Syntax_Syntax.Total
                    (t2,uu____23273)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23290 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23290 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23293,FStar_Syntax_Syntax.Total uu____23294) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23312),FStar_Syntax_Syntax.Total
                    (t2,uu____23314)) ->
                     let uu____23331 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23331 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23335),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23337)) ->
                     let uu____23354 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23354 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23358),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23360)) ->
                     let uu____23377 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____23377 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23380,FStar_Syntax_Syntax.Comp uu____23381) ->
                     let uu____23390 =
                       let uu___166_23395 = problem  in
                       let uu____23400 =
                         let uu____23401 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23401
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23395.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23400;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23395.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23395.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23395.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23395.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23395.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23395.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23395.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23395.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23390 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23402,FStar_Syntax_Syntax.Comp uu____23403) ->
                     let uu____23412 =
                       let uu___166_23417 = problem  in
                       let uu____23422 =
                         let uu____23423 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23423
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_23417.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23422;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_23417.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_23417.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_23417.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_23417.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_23417.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_23417.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_23417.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_23417.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23412 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23424,FStar_Syntax_Syntax.GTotal uu____23425) ->
                     let uu____23434 =
                       let uu___167_23439 = problem  in
                       let uu____23444 =
                         let uu____23445 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23445
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23439.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23439.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23439.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23444;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23439.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23439.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23439.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23439.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23439.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23439.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23434 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23446,FStar_Syntax_Syntax.Total uu____23447) ->
                     let uu____23456 =
                       let uu___167_23461 = problem  in
                       let uu____23466 =
                         let uu____23467 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23467
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_23461.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_23461.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_23461.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23466;
                         FStar_TypeChecker_Common.element =
                           (uu___167_23461.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_23461.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_23461.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_23461.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_23461.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_23461.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____23456 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23468,FStar_Syntax_Syntax.Comp uu____23469) ->
                     let uu____23470 =
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
                     if uu____23470
                     then
                       let uu____23471 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____23471 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____23477 =
                            let uu____23482 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____23482
                            then (c1_comp, c2_comp)
                            else
                              (let uu____23488 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____23489 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____23488, uu____23489))
                             in
                          match uu____23477 with
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
                           (let uu____23496 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23496
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23498 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____23498 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23501 =
                                  let uu____23502 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____23503 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____23502 uu____23503
                                   in
                                giveup env uu____23501 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23510 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23548  ->
              match uu____23548 with
              | (uu____23561,uu____23562,u,uu____23564,uu____23565,uu____23566)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23510 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____23599 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____23599 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____23617 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23645  ->
                match uu____23645 with
                | (u1,u2) ->
                    let uu____23652 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____23653 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____23652 uu____23653))
         in
      FStar_All.pipe_right uu____23617 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23674,[])) -> "{}"
      | uu____23699 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23716 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____23716
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23719 =
              FStar_List.map
                (fun uu____23729  ->
                   match uu____23729 with
                   | (uu____23734,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23719 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23739 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23739 imps
  
let new_t_problem :
  'Auu____23754 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____23754 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____23754)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____23794 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____23794
                then
                  let uu____23795 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____23796 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23795
                    (rel_to_string rel) uu____23796
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
            let uu____23828 =
              let uu____23831 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_72  -> FStar_Pervasives_Native.Some _0_72)
                uu____23831
               in
            FStar_Syntax_Syntax.new_bv uu____23828 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____23840 =
              let uu____23843 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_73  -> FStar_Pervasives_Native.Some _0_73)
                uu____23843
               in
            let uu____23846 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____23840 uu____23846  in
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
          let uu____23882 = FStar_Options.eager_inference ()  in
          if uu____23882
          then
            let uu___168_23883 = probs  in
            {
              attempting = (uu___168_23883.attempting);
              wl_deferred = (uu___168_23883.wl_deferred);
              ctr = (uu___168_23883.ctr);
              defer_ok = false;
              smt_ok = (uu___168_23883.smt_ok);
              tcenv = (uu___168_23883.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____23894 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____23894
              then
                let uu____23895 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____23895
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
          ((let uu____23913 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23913
            then
              let uu____23914 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23914
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____23918 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____23918
             then
               let uu____23919 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____23919
             else ());
            (let f2 =
               let uu____23922 =
                 let uu____23923 = FStar_Syntax_Util.unmeta f1  in
                 uu____23923.FStar_Syntax_Syntax.n  in
               match uu____23922 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____23927 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___169_23928 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___169_23928.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_23928.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_23928.FStar_TypeChecker_Env.implicits)
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
            let uu____23953 =
              let uu____23954 =
                let uu____23955 =
                  let uu____23956 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____23956
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____23955;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____23954  in
            FStar_All.pipe_left
              (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____23953
  
let with_guard_no_simp :
  'Auu____23987 .
    'Auu____23987 ->
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
            let uu____24010 =
              let uu____24011 =
                let uu____24012 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____24012
                  (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____24011;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____24010
  
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
          (let uu____24058 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____24058
           then
             let uu____24059 = FStar_Syntax_Print.term_to_string t1  in
             let uu____24060 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24059
               uu____24060
           else ());
          (let prob =
             let uu____24063 =
               let uu____24068 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24068
                in
             FStar_All.pipe_left
               (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
               uu____24063
              in
           let g =
             let uu____24076 =
               let uu____24079 = singleton' env prob smt_ok  in
               solve_and_commit env uu____24079
                 (fun uu____24081  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____24076  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24105 = try_teq true env t1 t2  in
        match uu____24105 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____24109 = FStar_TypeChecker_Env.get_range env  in
              let uu____24110 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____24109 uu____24110);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24117 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____24117
              then
                let uu____24118 = FStar_Syntax_Print.term_to_string t1  in
                let uu____24119 = FStar_Syntax_Print.term_to_string t2  in
                let uu____24120 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24118
                  uu____24119 uu____24120
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
          let uu____24142 = FStar_TypeChecker_Env.get_range env  in
          let uu____24143 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____24142 uu____24143
  
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
        (let uu____24168 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24168
         then
           let uu____24169 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____24170 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____24169 uu____24170
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____24174 =
             let uu____24179 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24179 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____24174
            in
         let uu____24184 =
           let uu____24187 = singleton env prob  in
           solve_and_commit env uu____24187
             (fun uu____24189  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____24184)
  
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
      fun uu____24224  ->
        match uu____24224 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24267 =
                 let uu____24272 =
                   let uu____24273 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____24274 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____24273 uu____24274
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____24272)  in
               let uu____24275 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____24267 uu____24275)
               in
            let equiv1 v1 v' =
              let uu____24287 =
                let uu____24292 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24293 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24292, uu____24293)  in
              match uu____24287 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24312 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24342 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24342 with
                      | FStar_Syntax_Syntax.U_unif uu____24349 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24378  ->
                                    match uu____24378 with
                                    | (u,v') ->
                                        let uu____24387 = equiv1 v1 v'  in
                                        if uu____24387
                                        then
                                          let uu____24390 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24390 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24406 -> []))
               in
            let uu____24411 =
              let wl =
                let uu___170_24415 = empty_worklist env  in
                {
                  attempting = (uu___170_24415.attempting);
                  wl_deferred = (uu___170_24415.wl_deferred);
                  ctr = (uu___170_24415.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_24415.smt_ok);
                  tcenv = (uu___170_24415.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24433  ->
                      match uu____24433 with
                      | (lb,v1) ->
                          let uu____24440 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24440 with
                           | USolved wl1 -> ()
                           | uu____24442 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24452 =
              match uu____24452 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24461) -> true
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
                      uu____24484,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24486,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24497) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24504,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24512 -> false)
               in
            let uu____24517 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24532  ->
                      match uu____24532 with
                      | (u,v1) ->
                          let uu____24539 = check_ineq (u, v1)  in
                          if uu____24539
                          then true
                          else
                            ((let uu____24542 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24542
                              then
                                let uu____24543 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24544 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24543
                                  uu____24544
                              else ());
                             false)))
               in
            if uu____24517
            then ()
            else
              ((let uu____24548 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____24548
                then
                  ((let uu____24550 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24550);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24560 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24560))
                else ());
               (let uu____24570 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____24570))
  
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
      let fail1 uu____24628 =
        match uu____24628 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____24642 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____24642
       then
         let uu____24643 = wl_to_string wl  in
         let uu____24644 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____24643 uu____24644
       else ());
      (let g1 =
         let uu____24659 = solve_and_commit env wl fail1  in
         match uu____24659 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___171_24672 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___171_24672.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_24672.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_24672.FStar_TypeChecker_Env.implicits)
             }
         | uu____24677 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___172_24681 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_24681.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_24681.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___172_24681.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____24709 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24709 with
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
            let uu___173_24832 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___173_24832.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___173_24832.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___173_24832.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24833 =
            let uu____24834 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24834  in
          if uu____24833
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____24842 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24843 =
                       let uu____24844 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24844
                        in
                     FStar_Errors.diag uu____24842 uu____24843)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____24848 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____24849 =
                        let uu____24850 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____24850
                         in
                      FStar_Errors.diag uu____24848 uu____24849)
                   else ();
                   (let uu____24853 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____24853 "discharge_guard'"
                      env vc1);
                   (let uu____24854 = check_trivial vc1  in
                    match uu____24854 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____24861 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24862 =
                                let uu____24863 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____24863
                                 in
                              FStar_Errors.diag uu____24861 uu____24862)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____24868 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24869 =
                                let uu____24870 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____24870
                                 in
                              FStar_Errors.diag uu____24868 uu____24869)
                           else ();
                           (let vcs =
                              let uu____24881 = FStar_Options.use_tactics ()
                                 in
                              if uu____24881
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____24901  ->
                                     (let uu____24903 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a239  -> ())
                                        uu____24903);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____24946  ->
                                              match uu____24946 with
                                              | (env1,goal,opts) ->
                                                  let uu____24962 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____24962, opts)))))
                              else
                                (let uu____24964 =
                                   let uu____24971 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____24971)  in
                                 [uu____24964])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____25004  ->
                                    match uu____25004 with
                                    | (env1,goal,opts) ->
                                        let uu____25014 = check_trivial goal
                                           in
                                        (match uu____25014 with
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
                                                (let uu____25022 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25023 =
                                                   let uu____25024 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____25025 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____25024 uu____25025
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25022 uu____25023)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____25028 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____25029 =
                                                   let uu____25030 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____25030
                                                    in
                                                 FStar_Errors.diag
                                                   uu____25028 uu____25029)
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
      let uu____25044 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25044 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____25051 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____25051
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____25062 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____25062 with
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
          let uu____25090 = FStar_Syntax_Unionfind.find u  in
          match uu____25090 with
          | FStar_Pervasives_Native.None  -> true
          | uu____25093 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____25115 = acc  in
          match uu____25115 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____25201 = hd1  in
                   (match uu____25201 with
                    | (uu____25214,env,u,tm,k,r) ->
                        let uu____25220 = unresolved u  in
                        if uu____25220
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___174_25250 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___174_25250.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___174_25250.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___174_25250.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___174_25250.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___174_25250.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___174_25250.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___174_25250.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___174_25250.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___174_25250.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___174_25250.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___174_25250.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___174_25250.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___174_25250.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___174_25250.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___174_25250.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___174_25250.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___174_25250.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___174_25250.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___174_25250.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___174_25250.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___174_25250.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___174_25250.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___174_25250.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___174_25250.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___174_25250.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___174_25250.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___174_25250.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___174_25250.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___174_25250.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___174_25250.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___174_25250.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___174_25250.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___174_25250.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___174_25250.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___174_25250.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___174_25250.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____25253 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____25253
                            then
                              let uu____25254 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____25255 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____25256 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____25254 uu____25255 uu____25256
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____25267 =
                                      let uu____25276 =
                                        let uu____25283 =
                                          let uu____25284 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____25285 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____25284 uu____25285
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____25283, r)
                                         in
                                      [uu____25276]  in
                                    FStar_Errors.add_errors uu____25267);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___177_25299 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___177_25299.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___177_25299.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___177_25299.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____25302 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25309  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____25302 with
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
        let uu___178_25337 = g  in
        let uu____25338 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___178_25337.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___178_25337.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___178_25337.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25338
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
        let uu____25400 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25400 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25413 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a240  -> ()) uu____25413
      | (reason,uu____25415,uu____25416,e,t,r)::uu____25420 ->
          let uu____25447 =
            let uu____25452 =
              let uu____25453 = FStar_Syntax_Print.term_to_string t  in
              let uu____25454 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25453 uu____25454
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25452)
             in
          FStar_Errors.raise_error uu____25447 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___179_25465 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_25465.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_25465.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_25465.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25492 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25492 with
      | FStar_Pervasives_Native.Some uu____25498 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25514 = try_teq false env t1 t2  in
        match uu____25514 with
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
        (let uu____25540 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25540
         then
           let uu____25541 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25542 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25541
             uu____25542
         else ());
        (let uu____25544 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25544 with
         | (prob,x) ->
             let g =
               let uu____25560 =
                 let uu____25563 = singleton' env prob true  in
                 solve_and_commit env uu____25563
                   (fun uu____25565  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25560  in
             ((let uu____25575 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____25575
               then
                 let uu____25576 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____25577 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____25578 =
                   let uu____25579 = FStar_Util.must g  in
                   guard_to_string env uu____25579  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____25576 uu____25577 uu____25578
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
        let uu____25613 = check_subtyping env t1 t2  in
        match uu____25613 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25632 =
              let uu____25633 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____25633 g  in
            FStar_Pervasives_Native.Some uu____25632
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25651 = check_subtyping env t1 t2  in
        match uu____25651 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25670 =
              let uu____25671 =
                let uu____25672 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25672]  in
              close_guard env uu____25671 g  in
            FStar_Pervasives_Native.Some uu____25670
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____25689 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25689
         then
           let uu____25690 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25691 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25690
             uu____25691
         else ());
        (let uu____25693 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____25693 with
         | (prob,x) ->
             let g =
               let uu____25703 =
                 let uu____25706 = singleton' env prob false  in
                 solve_and_commit env uu____25706
                   (fun uu____25708  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25703  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____25719 =
                      let uu____25720 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____25720]  in
                    close_guard env uu____25719 g1  in
                  discharge_guard_nosmt env g2))
  