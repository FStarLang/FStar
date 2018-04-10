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
                let uu____255 =
                  let uu____256 =
                    let uu____271 =
                      let uu____274 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____274]  in
                    (f, uu____271)  in
                  FStar_Syntax_Syntax.Tm_app uu____256  in
                FStar_Syntax_Syntax.mk uu____255  in
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
          let uu___120_296 = g  in
          let uu____297 =
            let uu____298 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____298  in
          {
            FStar_TypeChecker_Env.guard_f = uu____297;
            FStar_TypeChecker_Env.deferred =
              (uu___120_296.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___120_296.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___120_296.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____304 -> failwith "impossible"
  
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
          let uu____319 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____319
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____325 =
      let uu____326 = FStar_Syntax_Util.unmeta t  in
      uu____326.FStar_Syntax_Syntax.n  in
    match uu____325 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____330 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____371 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____371;
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
                       let uu____452 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____452
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___121_454 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___121_454.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___121_454.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___121_454.FStar_TypeChecker_Env.implicits)
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
               let uu____479 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____479
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
            let uu___122_498 = g  in
            let uu____499 =
              let uu____500 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____500  in
            {
              FStar_TypeChecker_Env.guard_f = uu____499;
              FStar_TypeChecker_Env.deferred =
                (uu___122_498.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___122_498.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___122_498.FStar_TypeChecker_Env.implicits)
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
        | uu____536 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____561 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____561  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____569 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____569, uv1)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____618 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____660 -> false
  
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
    match projectee with | Success _0 -> true | uu____860 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____878 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____903 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____909 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____915 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob = (FStar_Syntax_Syntax.comp,unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___88_940  ->
    match uu___88_940 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____948 =
        let uu____949 = FStar_Syntax_Subst.compress t  in
        uu____949.FStar_Syntax_Syntax.n  in
      match uu____948 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____978 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____979 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____978 uu____979
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____982;
             FStar_Syntax_Syntax.vars = uu____983;_},args)
          ->
          let uu____1029 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____1030 = FStar_Syntax_Print.term_to_string ty  in
          let uu____1031 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____1029 uu____1030 uu____1031
      | uu____1032 -> "--"  in
    let uu____1033 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____1033 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___89_1043  ->
      match uu___89_1043 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1049 =
            let uu____1052 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1053 =
              let uu____1056 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1057 =
                let uu____1060 =
                  let uu____1063 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1063]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1060
                 in
              uu____1056 :: uu____1057  in
            uu____1052 :: uu____1053  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1049
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1069 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1070 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1071 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1069 uu____1070
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1071
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___90_1081  ->
      match uu___90_1081 with
      | UNIV (u,t) ->
          let x =
            let uu____1085 = FStar_Options.hide_uvar_nums ()  in
            if uu____1085
            then "?"
            else
              (let uu____1087 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1087 FStar_Util.string_of_int)
             in
          let uu____1088 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1088
      | TERM ((u,uu____1090),t) ->
          let x =
            let uu____1097 = FStar_Options.hide_uvar_nums ()  in
            if uu____1097
            then "?"
            else
              (let uu____1099 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____1099 FStar_Util.string_of_int)
             in
          let uu____1100 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1100
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1115 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1115 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1129 =
      let uu____1132 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1132
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1129 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1145 .
    (FStar_Syntax_Syntax.term,'Auu____1145) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1163 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1181  ->
              match uu____1181 with
              | (x,uu____1187) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1163 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1195 =
      let uu____1196 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1196  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1195;
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
        let uu___123_1218 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___123_1218.wl_deferred);
          ctr = (uu___123_1218.ctr);
          defer_ok = (uu___123_1218.defer_ok);
          smt_ok;
          tcenv = (uu___123_1218.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1235 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1235,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___124_1258 = empty_worklist env  in
      let uu____1259 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1259;
        wl_deferred = (uu___124_1258.wl_deferred);
        ctr = (uu___124_1258.ctr);
        defer_ok = false;
        smt_ok = (uu___124_1258.smt_ok);
        tcenv = (uu___124_1258.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___125_1279 = wl  in
        {
          attempting = (uu___125_1279.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___125_1279.ctr);
          defer_ok = (uu___125_1279.defer_ok);
          smt_ok = (uu___125_1279.smt_ok);
          tcenv = (uu___125_1279.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___126_1300 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___126_1300.wl_deferred);
        ctr = (uu___126_1300.ctr);
        defer_ok = (uu___126_1300.defer_ok);
        smt_ok = (uu___126_1300.smt_ok);
        tcenv = (uu___126_1300.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1316 =
          let uu____1317 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Rel")
             in
          if uu____1317
          then
            let uu____1318 = prob_to_string env prob  in
            FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1318
          else ()  in
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___91_1324  ->
    match uu___91_1324 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1331 'Auu____1332 .
    ('Auu____1331,'Auu____1332) FStar_TypeChecker_Common.problem ->
      ('Auu____1331,'Auu____1332) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___127_1350 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___127_1350.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___127_1350.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___127_1350.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___127_1350.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___127_1350.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___127_1350.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___127_1350.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1361 'Auu____1362 .
    ('Auu____1361,'Auu____1362) FStar_TypeChecker_Common.problem ->
      ('Auu____1361,'Auu____1362) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___92_1385  ->
    match uu___92_1385 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___93_1413  ->
      match uu___93_1413 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___94_1418  ->
    match uu___94_1418 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___95_1433  ->
    match uu___95_1433 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___96_1450  ->
    match uu___96_1450 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___97_1467  ->
    match uu___97_1467 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___98_1486  ->
    match uu___98_1486 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let def_scope_wf :
  'Auu____1509 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1509) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1537 =
          let uu____1538 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1538  in
        if uu____1537
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1570)::bs ->
                 let uu____1582 =
                   def_check_closed_in rng msg prev
                     bv.FStar_Syntax_Syntax.sort
                    in
                 aux (FStar_List.append prev [bv]) bs
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
    let uu____1599 = def_scope_wf "p_scope" (p_loc prob) r  in r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1615 =
          let uu____1616 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1616  in
        if uu____1615
        then ()
        else
          (let uu____1618 =
             let uu____1621 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1621
              in
           def_check_closed_in (p_loc prob) msg uu____1618 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1650 =
        let uu____1651 =
          let uu____1652 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1652  in
        if uu____1651
        then ()
        else
          (let uu____1654 = p_scope prob  in
           def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1654)
         in
      let uu____1661 =
        let uu____1662 =
          FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob)  in
        def_check_scoped (Prims.strcat msg ".guard") prob uu____1662  in
      let uu____1667 =
        let uu____1668 =
          FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob)  in
        def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1668  in
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1678 =
            def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs
             in
          def_check_scoped (Prims.strcat msg ".rhs") prob
            p.FStar_TypeChecker_Common.rhs
      | uu____1679 -> let uu____1680 = ()  in ()
  
let (mk_eq2 :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun prob  ->
    fun t1  ->
      fun t2  ->
        let uu____1700 = FStar_Syntax_Util.type_u ()  in
        match uu____1700 with
        | (t_type,u) ->
            let uu____1707 =
              let uu____1712 = p_scope prob  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____1712 t_type  in
            (match uu____1707 with
             | (tt,uu____1714) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___99_1719  ->
    match uu___99_1719 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1743 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1743 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1757  ->
    let uu____1758 = FStar_Util.incr ctr  in FStar_ST.op_Bang ctr
  
let mk_problem :
  'Auu____1855 'Auu____1856 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1855 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1855 ->
              'Auu____1856 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1855,'Auu____1856)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1900 = next_pid ()  in
                let uu____1901 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1900;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1901;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1924 'Auu____1925 .
    FStar_TypeChecker_Env.env ->
      'Auu____1924 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1924 ->
            'Auu____1925 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1924,'Auu____1925)
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
                let uu____1970 = next_pid ()  in
                let uu____1971 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1970;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1971;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____1992 'Auu____1993 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1992 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1992 ->
            'Auu____1993 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1992,'Auu____1993) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2032 = next_pid ()  in
              let uu____2033 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____2032;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____2033;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____2044 .
    worklist ->
      ('Auu____2044,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____2104 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____2104
        then
          let uu____2105 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2106 = prob_to_string env d  in
          let uu____2107 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2105 uu____2106 uu____2107 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2113 -> failwith "impossible"  in
           let uu____2114 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2128 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2129 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2128, uu____2129)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2135 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2136 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2135, uu____2136)
              in
           match uu____2114 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___100_2154  ->
            match uu___100_2154 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2166 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____2168),t) ->
                let uu____2174 =
                  def_check_closed t.FStar_Syntax_Syntax.pos "commit" t  in
                FStar_Syntax_Util.set_uvar u t))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_2193  ->
           match uu___101_2193 with
           | UNIV uu____2196 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____2202),t) ->
               let uu____2208 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____2208
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
        (fun uu___102_2232  ->
           match uu___102_2232 with
           | UNIV (u',t) ->
               let uu____2237 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2237
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2241 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2252 =
        let uu____2253 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2253
         in
      FStar_Syntax_Subst.compress uu____2252
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2264 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2264
  
let norm_arg :
  'Auu____2271 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2271) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2271)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2294 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2294, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2329  ->
              match uu____2329 with
              | (x,imp) ->
                  let uu____2340 =
                    let uu___128_2341 = x  in
                    let uu____2342 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___128_2341.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___128_2341.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2342
                    }  in
                  (uu____2340, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2362 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2362
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2366 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2366
        | uu____2369 -> u2  in
      let uu____2370 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2370
  
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
                (let uu____2492 = norm_refinement env t12  in
                 match uu____2492 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2509;
                     FStar_Syntax_Syntax.vars = uu____2510;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2536 =
                       let uu____2537 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2538 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2537 uu____2538
                        in
                     failwith uu____2536)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2554 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2554
          | FStar_Syntax_Syntax.Tm_uinst uu____2555 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2592 =
                   let uu____2593 = FStar_Syntax_Subst.compress t1'  in
                   uu____2593.FStar_Syntax_Syntax.n  in
                 match uu____2592 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2610 -> aux true t1'
                 | uu____2617 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2632 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2663 =
                   let uu____2664 = FStar_Syntax_Subst.compress t1'  in
                   uu____2664.FStar_Syntax_Syntax.n  in
                 match uu____2663 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2681 -> aux true t1'
                 | uu____2688 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2703 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2748 =
                   let uu____2749 = FStar_Syntax_Subst.compress t1'  in
                   uu____2749.FStar_Syntax_Syntax.n  in
                 match uu____2748 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2766 -> aux true t1'
                 | uu____2773 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2788 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2803 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2818 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2833 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2848 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2875 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2906 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2927 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2958 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2985 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3022 ->
              let uu____3029 =
                let uu____3030 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3031 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3030 uu____3031
                 in
              failwith uu____3029
          | FStar_Syntax_Syntax.Tm_ascribed uu____3046 ->
              let uu____3073 =
                let uu____3074 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3075 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3074 uu____3075
                 in
              failwith uu____3073
          | FStar_Syntax_Syntax.Tm_delayed uu____3090 ->
              let uu____3115 =
                let uu____3116 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3117 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3116 uu____3117
                 in
              failwith uu____3115
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3132 =
                let uu____3133 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3134 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3133 uu____3134
                 in
              failwith uu____3132
           in
        let uu____3149 = whnf env t1  in aux false uu____3149
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3180 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3180 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3211 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3211 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3247 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3247, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3258 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3258 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3283 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3283 with
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
  fun uu____3364  ->
    match uu____3364 with
    | (t_base,refopt) ->
        let uu____3391 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3391 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3429 =
      let uu____3432 =
        let uu____3435 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3458  ->
                  match uu____3458 with | (uu____3465,uu____3466,x) -> x))
           in
        FStar_List.append wl.attempting uu____3435  in
      FStar_List.map (wl_prob_to_string wl) uu____3432  in
    FStar_All.pipe_right uu____3429 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3485 =
          let uu____3498 =
            let uu____3499 = FStar_Syntax_Subst.compress k  in
            uu____3499.FStar_Syntax_Syntax.n  in
          match uu____3498 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3552 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3552)
              else
                (let uu____3566 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3566 with
                 | (ys',t1,uu____3589) ->
                     let uu____3594 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3594))
          | uu____3635 ->
              let uu____3636 =
                let uu____3647 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3647)  in
              ((ys, t), uu____3636)
           in
        match uu____3485 with
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
                 let uu____3696 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3696 c  in
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
            let uu____3732 = def_check_prob "solve_prob'" prob  in
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi  in
            let uu____3735 = p_guard prob  in
            match uu____3735 with
            | (uu____3740,uv) ->
                let uu____3742 =
                  let uu____3743 =
                    let uu____3744 = FStar_Syntax_Subst.compress uv  in
                    uu____3744.FStar_Syntax_Syntax.n  in
                  match uu____3743 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      let uu____3775 =
                        let uu____3776 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____3776
                        then
                          let uu____3777 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____3778 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____3779 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3777
                            uu____3778 uu____3779
                        else ()  in
                      let uu____3781 =
                        def_check_closed (p_loc prob) "solve_prob'" phi1  in
                      FStar_Syntax_Util.set_uvar uvar phi1
                  | uu____3782 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ()
                   in
                let uu____3784 = commit uvis  in
                let uu___129_3785 = wl  in
                {
                  attempting = (uu___129_3785.attempting);
                  wl_deferred = (uu___129_3785.wl_deferred);
                  ctr = (wl.ctr + (Prims.parse_int "1"));
                  defer_ok = (uu___129_3785.defer_ok);
                  smt_ok = (uu___129_3785.smt_ok);
                  tcenv = (uu___129_3785.tcenv)
                }
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        let uu____3805 =
          let uu____3806 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
              (FStar_Options.Other "RelCheck")
             in
          if uu____3806
          then
            let uu____3807 = FStar_Util.string_of_int pid  in
            let uu____3808 =
              let uu____3809 = FStar_List.map (uvi_to_string wl.tcenv) sol
                 in
              FStar_All.pipe_right uu____3809 (FStar_String.concat ", ")  in
            FStar_Util.print2 "Solving %s: with %s\n" uu____3807 uu____3808
          else ()  in
        let uu____3815 = commit sol  in
        let uu___130_3816 = wl  in
        {
          attempting = (uu___130_3816.attempting);
          wl_deferred = (uu___130_3816.wl_deferred);
          ctr = (wl.ctr + (Prims.parse_int "1"));
          defer_ok = (uu___130_3816.defer_ok);
          smt_ok = (uu___130_3816.smt_ok);
          tcenv = (uu___130_3816.tcenv)
        }
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let uu____3845 = def_check_prob "solve_prob.prob" prob  in
          let uu____3846 =
            FStar_Util.iter_opt logical_guard
              (def_check_scoped "solve_prob.guard" prob)
             in
          let conj_guard1 t g =
            match (t, g) with
            | (uu____3866,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3878 = FStar_Syntax_Util.mk_conj t1 f  in
                FStar_Pervasives_Native.Some uu____3878
             in
          let uu____3883 =
            let uu____3884 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3884
            then
              let uu____3885 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3886 =
                let uu____3887 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3887 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3885 uu____3886
            else ()  in
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3926 =
          let uu____3933 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3933 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3926
          (FStar_Util.for_some
             (fun uu____3969  ->
                match uu____3969 with
                | (uv,uu____3975) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3988 'Auu____3989 .
    'Auu____3988 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3989)
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
            let uu____4025 = occurs wl uk t  in Prims.op_Negation uu____4025
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____4032 =
                 let uu____4033 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____4034 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4033 uu____4034
                  in
               FStar_Pervasives_Native.Some uu____4032)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____4051 'Auu____4052 .
    'Auu____4051 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____4052)
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
            let uu____4111 = occurs_check env wl uk t  in
            match uu____4111 with
            | (occurs_ok,msg) ->
                let uu____4142 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____4142, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____4169 'Auu____4170 .
    (FStar_Syntax_Syntax.bv,'Auu____4169) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4170) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____4170) FStar_Pervasives_Native.tuple2
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
      let uu____4257 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4311  ->
                fun uu____4312  ->
                  match (uu____4311, uu____4312) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4393 =
                        let uu____4394 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4394  in
                      if uu____4393
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4419 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4419
                         then
                           let uu____4432 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____4432)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4257 with | (isect,uu____4473) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4502 'Auu____4503 .
    (FStar_Syntax_Syntax.bv,'Auu____4502) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4503) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4560  ->
              fun uu____4561  ->
                match (uu____4560, uu____4561) with
                | ((a,uu____4579),(b,uu____4581)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4600 'Auu____4601 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4600) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4601)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4601)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4655 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4669  ->
                      match uu____4669 with
                      | (b,uu____4675) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4655
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4691 -> FStar_Pervasives_Native.None
  
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
            let uu____4770 = pat_var_opt env seen hd1  in
            (match uu____4770 with
             | FStar_Pervasives_Native.None  ->
                 let uu____4783 =
                   let uu____4784 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4784
                   then
                     let uu____4785 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4785
                   else ()  in
                 FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4805 =
      let uu____4806 = FStar_Syntax_Subst.compress t  in
      uu____4806.FStar_Syntax_Syntax.n  in
    match uu____4805 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4809 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4826;
           FStar_Syntax_Syntax.pos = uu____4827;
           FStar_Syntax_Syntax.vars = uu____4828;_},uu____4829)
        -> true
    | uu____4866 -> false
  
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
           FStar_Syntax_Syntax.pos = uu____4992;
           FStar_Syntax_Syntax.vars = uu____4993;_},args)
        -> (t, uv, k, args)
    | uu____5061 -> failwith "Not a flex-uvar"
  
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
      let uu____5142 = destruct_flex_t t  in
      match uu____5142 with
      | (t1,uv,k,args) ->
          let uu____5257 = pat_vars env [] args  in
          (match uu____5257 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____5355 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5438 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5475 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5481 -> false
  
let string_of_option :
  'Auu____5488 .
    ('Auu____5488 -> Prims.string) ->
      'Auu____5488 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___103_5503  ->
      match uu___103_5503 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5509 = f x  in Prims.strcat "Some " uu____5509
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___104_5514  ->
    match uu___104_5514 with
    | MisMatch (d1,d2) ->
        let uu____5525 =
          let uu____5526 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5527 =
            let uu____5528 =
              let uu____5529 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5529 ")"  in
            Prims.strcat ") (" uu____5528  in
          Prims.strcat uu____5526 uu____5527  in
        Prims.strcat "MisMatch (" uu____5525
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___105_5534  ->
    match uu___105_5534 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5549 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5579 = m2 ()  in
          (match uu____5579 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5594 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5607 ->
          let uu____5608 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5608 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5619 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5642 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5651 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5679 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5679
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5680 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5681 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5682 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5699 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5712 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5736) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5742,uu____5743) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5785) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5806;
             FStar_Syntax_Syntax.index = uu____5807;
             FStar_Syntax_Syntax.sort = t2;_},uu____5809)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5816 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5817 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5818 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5831 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5838 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5856 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5856
  
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
            let uu____5883 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5883
            then FullMatch
            else
              (let uu____5885 =
                 let uu____5894 =
                   let uu____5897 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5897  in
                 let uu____5898 =
                   let uu____5901 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5901  in
                 (uu____5894, uu____5898)  in
               MisMatch uu____5885)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5907),FStar_Syntax_Syntax.Tm_uinst (g,uu____5909)) ->
            let uu____5918 = head_matches env f g  in
            FStar_All.pipe_right uu____5918 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5921 = FStar_Const.eq_const c d  in
            if uu____5921
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5928),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5930)) ->
            let uu____5979 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5979
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5986),FStar_Syntax_Syntax.Tm_refine (y,uu____5988)) ->
            let uu____5997 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5997 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5999),uu____6000) ->
            let uu____6005 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6005 head_match
        | (uu____6006,FStar_Syntax_Syntax.Tm_refine (x,uu____6008)) ->
            let uu____6013 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6013 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6014,FStar_Syntax_Syntax.Tm_type
           uu____6015) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6016,FStar_Syntax_Syntax.Tm_arrow uu____6017) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6043),FStar_Syntax_Syntax.Tm_app (head',uu____6045))
            ->
            let uu____6086 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6086 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6088),uu____6089) ->
            let uu____6110 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6110 head_match
        | (uu____6111,FStar_Syntax_Syntax.Tm_app (head1,uu____6113)) ->
            let uu____6134 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6134 head_match
        | uu____6135 ->
            let uu____6140 =
              let uu____6149 = delta_depth_of_term env t11  in
              let uu____6152 = delta_depth_of_term env t21  in
              (uu____6149, uu____6152)  in
            MisMatch uu____6140
  
let head_matches_delta :
  'Auu____6169 .
    FStar_TypeChecker_Env.env ->
      'Auu____6169 ->
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
            let uu____6207 = FStar_Syntax_Util.head_and_args t  in
            match uu____6207 with
            | (head1,uu____6225) ->
                let uu____6246 =
                  let uu____6247 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6247.FStar_Syntax_Syntax.n  in
                (match uu____6246 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6253 =
                       let uu____6254 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6254 FStar_Option.isSome
                        in
                     if uu____6253
                     then
                       let uu____6273 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6273
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6277 -> FStar_Pervasives_Native.None)
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6389)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6407 =
                     let uu____6416 = maybe_inline t11  in
                     let uu____6419 = maybe_inline t21  in
                     (uu____6416, uu____6419)  in
                   match uu____6407 with
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
                (uu____6456,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6474 =
                     let uu____6483 = maybe_inline t11  in
                     let uu____6486 = maybe_inline t21  in
                     (uu____6483, uu____6486)  in
                   match uu____6474 with
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
                let uu____6529 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6529 with
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
                let uu____6552 =
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
                (match uu____6552 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6576 -> fail1 r
            | uu____6585 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          let uu____6597 =
            let uu____6598 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "RelDelta")
               in
            if uu____6598
            then
              let uu____6599 = FStar_Syntax_Print.term_to_string t1  in
              let uu____6600 = FStar_Syntax_Print.term_to_string t2  in
              let uu____6601 =
                string_of_match_result (FStar_Pervasives_Native.fst r)  in
              FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6599
                uu____6600 uu____6601
            else ()  in
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6643 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6687 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___106_6701  ->
    match uu___106_6701 with
    | T (t,uu____6703) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6727 = FStar_Syntax_Util.type_u ()  in
      match uu____6727 with
      | (t,uu____6733) ->
          let uu____6734 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6734
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6749 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6749 FStar_Pervasives_Native.fst
  
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
        let uu____6822 = head_matches env t1 t'  in
        match uu____6822 with
        | MisMatch uu____6823 -> false
        | uu____6832 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6931,imp),T (t2,uu____6934)) -> (t2, imp)
                     | uu____6957 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7024  ->
                    match uu____7024 with
                    | (t2,uu____7038) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7085 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7085 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7166))::tcs2) ->
                       aux
                         (((let uu___131_7205 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_7205.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_7205.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7223 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___107_7278 =
                 match uu___107_7278 with
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
               let uu____7397 = decompose1 [] bs1  in
               (rebuild, matches, uu____7397))
      | uu____7448 ->
          let rebuild uu___108_7455 =
            match uu___108_7455 with
            | [] -> t1
            | uu____7458 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___109_7493  ->
    match uu___109_7493 with
    | T (t,uu____7495) -> t
    | uu____7508 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___110_7513  ->
    match uu___110_7513 with
    | T (t,uu____7515) -> FStar_Syntax_Syntax.as_arg t
    | uu____7528 -> failwith "Impossible"
  
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
              | (uu____7657,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7686 = new_uvar r scope1 k  in
                  (match uu____7686 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7704 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7721 =
                         let uu____7722 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_23  ->
                              FStar_TypeChecker_Common.TProb _0_23)
                           uu____7722
                          in
                       ((T (gi_xs, mk_kind)), uu____7721))
              | (uu____7737,uu____7738,C uu____7739) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7889 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7906;
                         FStar_Syntax_Syntax.vars = uu____7907;_})
                        ->
                        let uu____7930 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7930 with
                         | (T (gi_xs,uu____7956),prob) ->
                             let uu____7970 =
                               let uu____7971 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_24  -> C _0_24)
                                 uu____7971
                                in
                             (uu____7970, [prob])
                         | uu____7974 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7989;
                         FStar_Syntax_Syntax.vars = uu____7990;_})
                        ->
                        let uu____8013 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____8013 with
                         | (T (gi_xs,uu____8039),prob) ->
                             let uu____8053 =
                               let uu____8054 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_25  -> C _0_25)
                                 uu____8054
                                in
                             (uu____8053, [prob])
                         | uu____8057 -> failwith "impossible")
                    | (uu____8068,uu____8069,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____8071;
                         FStar_Syntax_Syntax.vars = uu____8072;_})
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
                        let uu____8207 =
                          let uu____8216 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____8216 FStar_List.unzip
                           in
                        (match uu____8207 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8270 =
                                 let uu____8271 =
                                   let uu____8274 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____8274 un_T  in
                                 let uu____8275 =
                                   let uu____8284 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____8284
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8271;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8275;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8270
                                in
                             ((C gi_xs), sub_probs))
                    | uu____8293 ->
                        let uu____8306 = sub_prob scope1 args q  in
                        (match uu____8306 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7889 with
                   | (tc,probs) ->
                       let uu____8337 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8400,uu____8401),T
                            (t,uu____8403)) ->
                             let b1 =
                               ((let uu___132_8444 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___132_8444.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___132_8444.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8445 =
                               let uu____8452 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8452 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8445)
                         | uu____8487 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____8337 with
                        | (bopt,scope2,args1) ->
                            let uu____8571 = aux scope2 args1 qs2  in
                            (match uu____8571 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8609 =
                                           let uu____8612 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8612  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8609
                                          in
                                       let uu____8625 =
                                         def_check_closed (p_loc orig)
                                           "imitation_sub_probs (1)" f1
                                          in
                                       f1
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let f1 =
                                         let uu____8637 =
                                           let uu____8640 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8641 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8640 :: uu____8641  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8637
                                          in
                                       let uu____8654 =
                                         def_check_closed (p_loc orig)
                                           "imitation_sub_probs (2)" f1
                                          in
                                       f1
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
  'Auu____8713 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8713)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8713)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___133_8736 = p  in
      let uu____8741 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8742 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___133_8736.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8741;
        FStar_TypeChecker_Common.relation =
          (uu___133_8736.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8742;
        FStar_TypeChecker_Common.element =
          (uu___133_8736.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___133_8736.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___133_8736.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___133_8736.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___133_8736.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___133_8736.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8758 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8758
            (fun _0_26  -> FStar_TypeChecker_Common.TProb _0_26)
      | FStar_TypeChecker_Common.CProb uu____8767 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8791 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8791 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8801 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8801 with
           | (lh,uu____8821) ->
               let uu____8842 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8842 with
                | (rh,uu____8862) ->
                    let uu____8883 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8900,FStar_Syntax_Syntax.Tm_uvar uu____8901)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8938,uu____8939)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8960,FStar_Syntax_Syntax.Tm_uvar uu____8961)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8982,uu____8983)
                          ->
                          let uu____9000 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____9000 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9049 ->
                                    let rank =
                                      let uu____9057 = is_top_level_prob prob
                                         in
                                      if uu____9057
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____9059 =
                                      let uu___134_9064 = tp  in
                                      let uu____9069 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___134_9064.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___134_9064.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___134_9064.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9069;
                                        FStar_TypeChecker_Common.element =
                                          (uu___134_9064.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___134_9064.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___134_9064.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___134_9064.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___134_9064.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___134_9064.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____9059)))
                      | (uu____9080,FStar_Syntax_Syntax.Tm_uvar uu____9081)
                          ->
                          let uu____9098 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____9098 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9147 ->
                                    let uu____9154 =
                                      let uu___135_9161 = tp  in
                                      let uu____9166 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_9161.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9166;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_9161.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___135_9161.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_9161.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_9161.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_9161.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_9161.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_9161.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_9161.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____9154)))
                      | (uu____9183,uu____9184) -> (rigid_rigid, tp)  in
                    (match uu____8883 with
                     | (rank,tp1) ->
                         let uu____9203 =
                           FStar_All.pipe_right
                             (let uu___136_9209 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___136_9209.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___136_9209.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___136_9209.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___136_9209.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___136_9209.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___136_9209.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___136_9209.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___136_9209.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___136_9209.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_27  ->
                                FStar_TypeChecker_Common.TProb _0_27)
                            in
                         (rank, uu____9203))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9219 =
            FStar_All.pipe_right
              (let uu___137_9225 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_9225.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_9225.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_9225.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_9225.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_9225.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_9225.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___137_9225.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_9225.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_9225.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_28  -> FStar_TypeChecker_Common.CProb _0_28)
             in
          (rigid_rigid, uu____9219)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____9284 probs =
      match uu____9284 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9337 = rank wl hd1  in
               (match uu____9337 with
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
    match projectee with | UDeferred _0 -> true | uu____9450 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9464 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9478 -> false
  
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
                        let uu____9528 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9528 with
                        | (k,uu____9534) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9544 -> false)))
            | uu____9545 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9595 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9601 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9601 = (Prims.parse_int "0")))
                           in
                        if uu____9595 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9616 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9622 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9622 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9616)
               in
            let uu____9623 = filter1 u12  in
            let uu____9626 = filter1 u22  in (uu____9623, uu____9626)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9652 = filter_out_common_univs us1 us2  in
                (match uu____9652 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9708 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9708 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9711 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9721 =
                          let uu____9722 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9723 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9722
                            uu____9723
                           in
                        UFailed uu____9721))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9745 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9745 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9769 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9769 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9772 ->
                let uu____9777 =
                  let uu____9778 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9779 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9778
                    uu____9779 msg
                   in
                UFailed uu____9777
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9780,uu____9781) ->
              let uu____9782 =
                let uu____9783 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9784 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9783 uu____9784
                 in
              failwith uu____9782
          | (FStar_Syntax_Syntax.U_unknown ,uu____9785) ->
              let uu____9786 =
                let uu____9787 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9788 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9787 uu____9788
                 in
              failwith uu____9786
          | (uu____9789,FStar_Syntax_Syntax.U_bvar uu____9790) ->
              let uu____9791 =
                let uu____9792 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9793 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9792 uu____9793
                 in
              failwith uu____9791
          | (uu____9794,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9795 =
                let uu____9796 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9797 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9796 uu____9797
                 in
              failwith uu____9795
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9821 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9821
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9843 = occurs_univ v1 u3  in
              if uu____9843
              then
                let uu____9844 =
                  let uu____9845 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9846 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9845 uu____9846
                   in
                try_umax_components u11 u21 uu____9844
              else
                (let uu____9848 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9848)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9868 = occurs_univ v1 u3  in
              if uu____9868
              then
                let uu____9869 =
                  let uu____9870 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9871 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9870 uu____9871
                   in
                try_umax_components u11 u21 uu____9869
              else
                (let uu____9873 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9873)
          | (FStar_Syntax_Syntax.U_max uu____9882,uu____9883) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9889 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9889
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9891,FStar_Syntax_Syntax.U_max uu____9892) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9898 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9898
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9900,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9901,FStar_Syntax_Syntax.U_name
             uu____9902) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9903) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9904) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9905,FStar_Syntax_Syntax.U_succ
             uu____9906) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9907,FStar_Syntax_Syntax.U_zero
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
      let uu____10007 = bc1  in
      match uu____10007 with
      | (bs1,mk_cod1) ->
          let uu____10051 = bc2  in
          (match uu____10051 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10160 = aux xs ys  in
                     (match uu____10160 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10243 =
                       let uu____10250 = mk_cod1 xs  in ([], uu____10250)  in
                     let uu____10253 =
                       let uu____10260 = mk_cod2 ys  in ([], uu____10260)  in
                     (uu____10243, uu____10253)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      let uu____10444 =
        let uu____10445 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "RelCheck")
           in
        if uu____10445
        then
          let uu____10446 = wl_to_string probs  in
          FStar_Util.print1 "solve:\n\t%s\n" uu____10446
        else ()  in
      let uu____10448 = next_prob probs  in
      match uu____10448 with
      | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
          let probs1 =
            let uu___138_10469 = probs  in
            {
              attempting = tl1;
              wl_deferred = (uu___138_10469.wl_deferred);
              ctr = (uu___138_10469.ctr);
              defer_ok = (uu___138_10469.defer_ok);
              smt_ok = (uu___138_10469.smt_ok);
              tcenv = (uu___138_10469.tcenv)
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
                 let uu____10480 = solve_flex_rigid_join env tp probs1  in
                 (match uu____10480 with
                  | FStar_Pervasives_Native.None  ->
                      solve_t' env (maybe_invert tp) probs1
                  | FStar_Pervasives_Native.Some wl -> solve env wl)
               else
                 if
                   ((Prims.op_Negation probs1.defer_ok) &&
                      (rigid_flex <= rank1))
                     && (rank1 <= refine_flex)
                 then
                   (let uu____10485 = solve_rigid_flex_meet env tp probs1  in
                    match uu____10485 with
                    | FStar_Pervasives_Native.None  ->
                        solve_t' env (maybe_invert tp) probs1
                    | FStar_Pervasives_Native.Some wl -> solve env wl)
                 else solve_t' env (maybe_invert tp) probs1)
      | (FStar_Pervasives_Native.None ,uu____10490,uu____10491) ->
          (match probs.wl_deferred with
           | [] -> Success []
           | uu____10508 ->
               let uu____10517 =
                 FStar_All.pipe_right probs.wl_deferred
                   (FStar_List.partition
                      (fun uu____10576  ->
                         match uu____10576 with
                         | (c,uu____10584,uu____10585) -> c < probs.ctr))
                  in
               (match uu____10517 with
                | (attempt1,rest) ->
                    (match attempt1 with
                     | [] ->
                         let uu____10626 =
                           FStar_List.map
                             (fun uu____10641  ->
                                match uu____10641 with
                                | (uu____10652,x,y) -> (x, y))
                             probs.wl_deferred
                            in
                         Success uu____10626
                     | uu____10655 ->
                         let uu____10664 =
                           let uu___139_10665 = probs  in
                           let uu____10666 =
                             FStar_All.pipe_right attempt1
                               (FStar_List.map
                                  (fun uu____10687  ->
                                     match uu____10687 with
                                     | (uu____10694,uu____10695,y) -> y))
                              in
                           {
                             attempting = uu____10666;
                             wl_deferred = rest;
                             ctr = (uu___139_10665.ctr);
                             defer_ok = (uu___139_10665.defer_ok);
                             smt_ok = (uu___139_10665.smt_ok);
                             tcenv = (uu___139_10665.tcenv)
                           }  in
                         solve env uu____10664)))

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
            let uu____10702 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10702 with
            | USolved wl1 ->
                let uu____10704 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10704
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
                  let uu____10753 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10753 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10756 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10768;
                  FStar_Syntax_Syntax.vars = uu____10769;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10772;
                  FStar_Syntax_Syntax.vars = uu____10773;_},us2))
                ->
                let b = FStar_Syntax_Syntax.fv_eq f g  in
                let uu____10784 = ()  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10785,uu____10786) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10793,FStar_Syntax_Syntax.Tm_uinst uu____10794) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10801 -> USolved wl

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
            let uu____10810 =
              let uu____10811 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10811
              then
                let uu____10812 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10812 msg
              else ()  in
            solve env (defer msg orig wl)
          else giveup env msg orig

and (solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        let uu____10820 =
          let uu____10821 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "RelCheck")
             in
          if uu____10821
          then
            let uu____10822 =
              FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
            FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
              uu____10822
          else ()  in
        let uu____10824 =
          FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs  in
        match uu____10824 with
        | (u,args) ->
            let rec disjoin t1 t2 =
              let uu____10888 = head_matches_delta env () t1 t2  in
              match uu____10888 with
              | (mr,ts) ->
                  (match mr with
                   | MisMatch uu____10929 -> FStar_Pervasives_Native.None
                   | FullMatch  ->
                       (match ts with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.Some (t1, [])
                        | FStar_Pervasives_Native.Some (t11,t21) ->
                            FStar_Pervasives_Native.Some (t11, []))
                   | HeadMatch  ->
                       let uu____10978 =
                         match ts with
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             let uu____10993 =
                               FStar_Syntax_Subst.compress t11  in
                             let uu____10994 =
                               FStar_Syntax_Subst.compress t21  in
                             (uu____10993, uu____10994)
                         | FStar_Pervasives_Native.None  ->
                             let uu____10999 = FStar_Syntax_Subst.compress t1
                                in
                             let uu____11000 = FStar_Syntax_Subst.compress t2
                                in
                             (uu____10999, uu____11000)
                          in
                       (match uu____10978 with
                        | (t11,t21) ->
                            let eq_prob t12 t22 =
                              let uu____11028 =
                                new_problem env t12
                                  FStar_TypeChecker_Common.EQ t22
                                  FStar_Pervasives_Native.None
                                  t12.FStar_Syntax_Syntax.pos
                                  "meeting refinements"
                                 in
                              FStar_All.pipe_left
                                (fun _0_29  ->
                                   FStar_TypeChecker_Common.TProb _0_29)
                                uu____11028
                               in
                            (match ((t11.FStar_Syntax_Syntax.n),
                                     (t21.FStar_Syntax_Syntax.n))
                             with
                             | (FStar_Syntax_Syntax.Tm_refine
                                (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                (y,phi2)) ->
                                 let uu____11059 =
                                   let uu____11068 =
                                     let uu____11071 =
                                       let uu____11076 =
                                         let uu____11077 =
                                           let uu____11084 =
                                             FStar_Syntax_Util.mk_disj phi1
                                               phi2
                                              in
                                           (x, uu____11084)  in
                                         FStar_Syntax_Syntax.Tm_refine
                                           uu____11077
                                          in
                                       FStar_Syntax_Syntax.mk uu____11076  in
                                     uu____11071 FStar_Pervasives_Native.None
                                       t11.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____11092 =
                                     let uu____11095 =
                                       eq_prob x.FStar_Syntax_Syntax.sort
                                         y.FStar_Syntax_Syntax.sort
                                        in
                                     [uu____11095]  in
                                   (uu____11068, uu____11092)  in
                                 FStar_Pervasives_Native.Some uu____11059
                             | (uu____11108,FStar_Syntax_Syntax.Tm_refine
                                (x,uu____11110)) ->
                                 let uu____11115 =
                                   let uu____11122 =
                                     let uu____11125 =
                                       eq_prob x.FStar_Syntax_Syntax.sort t11
                                        in
                                     [uu____11125]  in
                                   (t11, uu____11122)  in
                                 FStar_Pervasives_Native.Some uu____11115
                             | (FStar_Syntax_Syntax.Tm_refine
                                (x,uu____11135),uu____11136) ->
                                 let uu____11141 =
                                   let uu____11148 =
                                     let uu____11151 =
                                       eq_prob x.FStar_Syntax_Syntax.sort t21
                                        in
                                     [uu____11151]  in
                                   (t21, uu____11148)  in
                                 FStar_Pervasives_Native.Some uu____11141
                             | uu____11160 ->
                                 let uu____11165 =
                                   FStar_Syntax_Util.head_and_args t11  in
                                 (match uu____11165 with
                                  | (head1,uu____11189) ->
                                      let uu____11210 =
                                        let uu____11211 =
                                          FStar_Syntax_Util.un_uinst head1
                                           in
                                        uu____11211.FStar_Syntax_Syntax.n  in
                                      (match uu____11210 with
                                       | FStar_Syntax_Syntax.Tm_fvar
                                           {
                                             FStar_Syntax_Syntax.fv_name =
                                               uu____11222;
                                             FStar_Syntax_Syntax.fv_delta =
                                               FStar_Syntax_Syntax.Delta_defined_at_level
                                               i;
                                             FStar_Syntax_Syntax.fv_qual =
                                               uu____11224;_}
                                           ->
                                           let prev =
                                             if i > (Prims.parse_int "1")
                                             then
                                               FStar_Syntax_Syntax.Delta_defined_at_level
                                                 (i - (Prims.parse_int "1"))
                                             else
                                               FStar_Syntax_Syntax.Delta_constant
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
                                       | uu____11231 ->
                                           FStar_Pervasives_Native.None)))))
               in
            let tt = u  in
            (match tt.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11244) ->
                 let uu____11269 =
                   FStar_All.pipe_right wl.attempting
                     (FStar_List.partition
                        (fun uu___111_11295  ->
                           match uu___111_11295 with
                           | FStar_TypeChecker_Common.TProb tp1 ->
                               (match tp1.FStar_TypeChecker_Common.rank with
                                | FStar_Pervasives_Native.Some rank1 when
                                    is_rigid_flex rank1 ->
                                    let uu____11302 =
                                      FStar_Syntax_Util.head_and_args
                                        tp1.FStar_TypeChecker_Common.rhs
                                       in
                                    (match uu____11302 with
                                     | (u',uu____11318) ->
                                         let uu____11339 =
                                           let uu____11340 = whnf env u'  in
                                           uu____11340.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____11339 with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv',uu____11344) ->
                                              FStar_Syntax_Unionfind.equiv uv
                                                uv'
                                          | uu____11369 -> false))
                                | uu____11370 -> false)
                           | uu____11373 -> false))
                    in
                 (match uu____11269 with
                  | (lower_bounds,rest) ->
                      let rec make_lower_bound uu____11409 tps =
                        match uu____11409 with
                        | (bound,sub_probs) ->
                            (match tps with
                             | [] ->
                                 FStar_Pervasives_Native.Some
                                   (bound, sub_probs)
                             | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                 let uu____11457 =
                                   let uu____11466 =
                                     whnf env
                                       hd1.FStar_TypeChecker_Common.lhs
                                      in
                                   disjoin bound uu____11466  in
                                 (match uu____11457 with
                                  | FStar_Pervasives_Native.Some
                                      (bound1,sub1) ->
                                      make_lower_bound
                                        (bound1,
                                          (FStar_List.append sub1 sub_probs))
                                        tl1
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Pervasives_Native.None)
                             | uu____11501 -> FStar_Pervasives_Native.None)
                         in
                      let uu____11510 =
                        let uu____11519 =
                          let uu____11526 =
                            whnf env tp.FStar_TypeChecker_Common.lhs  in
                          (uu____11526, [])  in
                        make_lower_bound uu____11519 lower_bounds  in
                      (match uu____11510 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____11537 =
                             let uu____11538 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "RelCheck")
                                in
                             if uu____11538
                             then FStar_Util.print_string "No lower bounds\n"
                             else ()  in
                           FStar_Pervasives_Native.None
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
                           let uu____11557 =
                             let uu____11558 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "RelCheck")
                                in
                             if uu____11558
                             then
                               let wl' =
                                 let uu___140_11560 = wl  in
                                 {
                                   attempting =
                                     ((FStar_TypeChecker_Common.TProb eq_prob)
                                     :: sub_probs);
                                   wl_deferred = (uu___140_11560.wl_deferred);
                                   ctr = (uu___140_11560.ctr);
                                   defer_ok = (uu___140_11560.defer_ok);
                                   smt_ok = (uu___140_11560.smt_ok);
                                   tcenv = (uu___140_11560.tcenv)
                                 }  in
                               let uu____11561 = wl_to_string wl'  in
                               FStar_Util.print1
                                 "After meeting refinements: %s\n"
                                 uu____11561
                             else ()  in
                           let uu____11563 =
                             solve_t env eq_prob
                               (let uu___141_11565 = wl  in
                                {
                                  attempting = sub_probs;
                                  wl_deferred = (uu___141_11565.wl_deferred);
                                  ctr = (uu___141_11565.ctr);
                                  defer_ok = (uu___141_11565.defer_ok);
                                  smt_ok = (uu___141_11565.smt_ok);
                                  tcenv = (uu___141_11565.tcenv)
                                })
                              in
                           (match uu____11563 with
                            | Success uu____11568 ->
                                let wl1 =
                                  let uu___142_11570 = wl  in
                                  {
                                    attempting = rest;
                                    wl_deferred =
                                      (uu___142_11570.wl_deferred);
                                    ctr = (uu___142_11570.ctr);
                                    defer_ok = (uu___142_11570.defer_ok);
                                    smt_ok = (uu___142_11570.smt_ok);
                                    tcenv = (uu___142_11570.tcenv)
                                  }  in
                                let wl2 =
                                  solve_prob' false
                                    (FStar_TypeChecker_Common.TProb tp)
                                    FStar_Pervasives_Native.None [] wl1
                                   in
                                let uu____11572 =
                                  FStar_List.fold_left
                                    (fun wl3  ->
                                       fun p  ->
                                         solve_prob' true p
                                           FStar_Pervasives_Native.None []
                                           wl3) wl2 lower_bounds
                                   in
                                FStar_Pervasives_Native.Some wl2
                            | uu____11577 -> FStar_Pervasives_Native.None)))
             | uu____11578 -> failwith "Impossible: Not a rigid-flex")

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        let uu____11586 =
          let uu____11587 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "RelCheck")
             in
          if uu____11587
          then
            let uu____11588 =
              FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
            FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
              uu____11588
          else ()  in
        let uu____11590 =
          FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs  in
        match uu____11590 with
        | (u,args) ->
            let uu____11629 =
              ((Prims.parse_int "0"), (Prims.parse_int "1"),
                (Prims.parse_int "2"), (Prims.parse_int "3"),
                (Prims.parse_int "4"))
               in
            (match uu____11629 with
             | (ok,head_match1,partial_match,fallback,failed_match) ->
                 let max1 i j = if i < j then j else i  in
                 let base_types_match t1 t2 =
                   let uu____11674 = FStar_Syntax_Util.head_and_args t1  in
                   match uu____11674 with
                   | (h1,args1) ->
                       let uu____11715 = FStar_Syntax_Util.head_and_args t2
                          in
                       (match uu____11715 with
                        | (h2,uu____11735) ->
                            (match ((h1.FStar_Syntax_Syntax.n),
                                     (h2.FStar_Syntax_Syntax.n))
                             with
                             | (FStar_Syntax_Syntax.Tm_fvar
                                tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                 let uu____11762 =
                                   FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                 if uu____11762
                                 then
                                   (if
                                      (FStar_List.length args1) =
                                        (Prims.parse_int "0")
                                    then FStar_Pervasives_Native.Some []
                                    else
                                      (let uu____11780 =
                                         let uu____11783 =
                                           let uu____11784 =
                                             new_problem env t1
                                               FStar_TypeChecker_Common.EQ t2
                                               FStar_Pervasives_Native.None
                                               t1.FStar_Syntax_Syntax.pos
                                               "joining refinements"
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_30  ->
                                                FStar_TypeChecker_Common.TProb
                                                  _0_30) uu____11784
                                            in
                                         [uu____11783]  in
                                       FStar_Pervasives_Native.Some
                                         uu____11780))
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
                                      (let uu____11817 =
                                         let uu____11820 =
                                           let uu____11821 =
                                             new_problem env t1
                                               FStar_TypeChecker_Common.EQ t2
                                               FStar_Pervasives_Native.None
                                               t1.FStar_Syntax_Syntax.pos
                                               "joining refinements"
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_31  ->
                                                FStar_TypeChecker_Common.TProb
                                                  _0_31) uu____11821
                                            in
                                         [uu____11820]  in
                                       FStar_Pervasives_Native.Some
                                         uu____11817))
                                 else FStar_Pervasives_Native.None
                             | uu____11835 -> FStar_Pervasives_Native.None))
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
                            let uu____11927 =
                              let uu____11936 =
                                let uu____11939 =
                                  FStar_Syntax_Util.mk_conj phi11 phi21  in
                                FStar_Syntax_Util.refine x1 uu____11939  in
                              (uu____11936, m1)  in
                            FStar_Pervasives_Native.Some uu____11927)
                   | (uu____11952,FStar_Syntax_Syntax.Tm_refine
                      (y,uu____11954)) ->
                       let m = base_types_match t1 y.FStar_Syntax_Syntax.sort
                          in
                       (match m with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some m1 ->
                            FStar_Pervasives_Native.Some (t2, m1))
                   | (FStar_Syntax_Syntax.Tm_refine
                      (x,uu____12002),uu____12003) ->
                       let m = base_types_match x.FStar_Syntax_Syntax.sort t2
                          in
                       (match m with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some m1 ->
                            FStar_Pervasives_Native.Some (t1, m1))
                   | uu____12050 ->
                       let m = base_types_match t1 t2  in
                       (match m with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some m1 ->
                            FStar_Pervasives_Native.Some (t1, m1))
                    in
                 let tt = u  in
                 (match tt.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12103) ->
                      let uu____12128 =
                        FStar_All.pipe_right wl.attempting
                          (FStar_List.partition
                             (fun uu___112_12154  ->
                                match uu___112_12154 with
                                | FStar_TypeChecker_Common.TProb tp1 ->
                                    (match tp1.FStar_TypeChecker_Common.rank
                                     with
                                     | FStar_Pervasives_Native.Some rank1
                                         when is_flex_rigid rank1 ->
                                         let uu____12161 =
                                           FStar_Syntax_Util.head_and_args
                                             tp1.FStar_TypeChecker_Common.lhs
                                            in
                                         (match uu____12161 with
                                          | (u',uu____12177) ->
                                              let uu____12198 =
                                                let uu____12199 = whnf env u'
                                                   in
                                                uu____12199.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____12198 with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   (uv',uu____12203) ->
                                                   FStar_Syntax_Unionfind.equiv
                                                     uv uv'
                                               | uu____12228 -> false))
                                     | uu____12229 -> false)
                                | uu____12232 -> false))
                         in
                      (match uu____12128 with
                       | (upper_bounds,rest) ->
                           let rec make_upper_bound uu____12272 tps =
                             match uu____12272 with
                             | (bound,sub_probs) ->
                                 (match tps with
                                  | [] ->
                                      FStar_Pervasives_Native.Some
                                        (bound, sub_probs)
                                  | (FStar_TypeChecker_Common.TProb hd1)::tl1
                                      ->
                                      let uu____12334 =
                                        let uu____12345 =
                                          whnf env
                                            hd1.FStar_TypeChecker_Common.rhs
                                           in
                                        conjoin bound uu____12345  in
                                      (match uu____12334 with
                                       | FStar_Pervasives_Native.Some
                                           (bound1,sub1) ->
                                           make_upper_bound
                                             (bound1,
                                               (FStar_List.append sub1
                                                  sub_probs)) tl1
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None)
                                  | uu____12396 ->
                                      FStar_Pervasives_Native.None)
                              in
                           let uu____12407 =
                             let uu____12418 =
                               let uu____12427 =
                                 whnf env tp.FStar_TypeChecker_Common.rhs  in
                               (uu____12427, [])  in
                             make_upper_bound uu____12418 upper_bounds  in
                           (match uu____12407 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____12440 =
                                  let uu____12441 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "RelCheck")
                                     in
                                  if uu____12441
                                  then
                                    FStar_Util.print_string
                                      "No upper bounds\n"
                                  else ()  in
                                FStar_Pervasives_Native.None
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
                                let uu____12466 =
                                  let uu____12467 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "RelCheck")
                                     in
                                  if uu____12467
                                  then
                                    let wl' =
                                      let uu___143_12469 = wl  in
                                      {
                                        attempting =
                                          ((FStar_TypeChecker_Common.TProb
                                              eq_prob) :: sub_probs);
                                        wl_deferred =
                                          (uu___143_12469.wl_deferred);
                                        ctr = (uu___143_12469.ctr);
                                        defer_ok = (uu___143_12469.defer_ok);
                                        smt_ok = (uu___143_12469.smt_ok);
                                        tcenv = (uu___143_12469.tcenv)
                                      }  in
                                    let uu____12470 = wl_to_string wl'  in
                                    FStar_Util.print1
                                      "After joining refinements: %s\n"
                                      uu____12470
                                  else ()  in
                                let uu____12472 =
                                  solve_t env eq_prob
                                    (let uu___144_12474 = wl  in
                                     {
                                       attempting = sub_probs;
                                       wl_deferred =
                                         (uu___144_12474.wl_deferred);
                                       ctr = (uu___144_12474.ctr);
                                       defer_ok = (uu___144_12474.defer_ok);
                                       smt_ok = (uu___144_12474.smt_ok);
                                       tcenv = (uu___144_12474.tcenv)
                                     })
                                   in
                                (match uu____12472 with
                                 | Success uu____12477 ->
                                     let wl1 =
                                       let uu___145_12479 = wl  in
                                       {
                                         attempting = rest;
                                         wl_deferred =
                                           (uu___145_12479.wl_deferred);
                                         ctr = (uu___145_12479.ctr);
                                         defer_ok = (uu___145_12479.defer_ok);
                                         smt_ok = (uu___145_12479.smt_ok);
                                         tcenv = (uu___145_12479.tcenv)
                                       }  in
                                     let wl2 =
                                       solve_prob' false
                                         (FStar_TypeChecker_Common.TProb tp)
                                         FStar_Pervasives_Native.None [] wl1
                                        in
                                     let uu____12481 =
                                       FStar_List.fold_left
                                         (fun wl3  ->
                                            fun p  ->
                                              solve_prob' true p
                                                FStar_Pervasives_Native.None
                                                [] wl3) wl2 upper_bounds
                                        in
                                     FStar_Pervasives_Native.Some wl2
                                 | uu____12486 ->
                                     FStar_Pervasives_Native.None)))
                  | uu____12487 -> failwith "Impossible: Not a flex-rigid"))

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
              let uu____12504 =
                let uu____12505 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12505
                then
                  let uu____12506 =
                    FStar_Syntax_Print.binders_to_string ", " bs1  in
                  let uu____12507 =
                    FStar_Syntax_Print.binders_to_string ", " bs2  in
                  FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                    uu____12506 (rel_to_string (p_rel orig)) uu____12507
                else ()  in
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs scope env1 subst1  in
                    let uu____12571 =
                      let uu____12572 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12572
                      then
                        let uu____12573 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____12573
                      else ()  in
                    let formula =
                      FStar_All.pipe_right (p_guard rhs_prob)
                        FStar_Pervasives_Native.fst
                       in
                    FStar_Util.Inl ([rhs_prob], formula)
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___146_12627 = hd1  in
                      let uu____12628 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___146_12627.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___146_12627.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12628
                      }  in
                    let hd21 =
                      let uu___147_12632 = hd2  in
                      let uu____12633 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___147_12632.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___147_12632.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12633
                      }  in
                    let prob =
                      let uu____12637 =
                        let uu____12642 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12642 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
                        uu____12637
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____12653 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12653
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____12657 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____12657 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12695 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____12700 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____12695 uu____12700
                            in
                         let uu____12709 =
                           let uu____12710 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12710
                           then
                             let uu____12711 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____12712 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12711 uu____12712
                           else ()  in
                         FStar_Util.Inl ((prob :: sub_probs), phi1)
                     | fail1 -> fail1)
                | uu____12735 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____12745 = aux scope env [] bs1 bs2  in
              match uu____12745 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                     in
                  solve env (attempt sub_probs wl1)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____12769 =
          def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem)
           in
        let uu____12770 = compress_tprob wl problem  in
        solve_t' env uu____12770 wl

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____12774 =
          def_check_prob "solve_t'.1"
            (FStar_TypeChecker_Common.TProb problem)
           in
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12813 = head_matches_delta env1 wl1 t1 t2  in
          match uu____12813 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12844,uu____12845) ->
                   let rec may_relate head3 =
                     let uu____12871 =
                       let uu____12872 = FStar_Syntax_Subst.compress head3
                          in
                       uu____12872.FStar_Syntax_Syntax.n  in
                     match uu____12871 with
                     | FStar_Syntax_Syntax.Tm_name uu____12875 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12876 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12899;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12900;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12903;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12904;
                           FStar_Syntax_Syntax.fv_qual = uu____12905;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12909,uu____12910) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12952) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12958) ->
                         may_relate t
                     | uu____12963 -> false  in
                   let uu____12964 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____12964
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
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11
                                   in
                                let uu____12983 =
                                  let uu____12984 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12984 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____12983
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____12986 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____12986
                   else
                     (let uu____12988 =
                        let uu____12989 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12990 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12989 uu____12990
                         in
                      giveup env1 uu____12988 orig)
               | (uu____12991,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___148_13005 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___148_13005.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___148_13005.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___148_13005.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___148_13005.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___148_13005.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___148_13005.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___148_13005.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___148_13005.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____13006,FStar_Pervasives_Native.None ) ->
                   let uu____13017 =
                     let uu____13018 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____13018
                     then
                       let uu____13019 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13020 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____13021 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____13022 = FStar_Syntax_Print.tag_of_term t2
                          in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____13019
                         uu____13020 uu____13021 uu____13022
                     else ()  in
                   let uu____13024 = FStar_Syntax_Util.head_and_args t1  in
                   (match uu____13024 with
                    | (head11,args1) ->
                        let uu____13061 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____13061 with
                         | (head21,args2) ->
                             let nargs = FStar_List.length args1  in
                             if nargs <> (FStar_List.length args2)
                             then
                               let uu____13115 =
                                 let uu____13116 =
                                   FStar_Syntax_Print.term_to_string head11
                                    in
                                 let uu____13117 = args_to_string args1  in
                                 let uu____13118 =
                                   FStar_Syntax_Print.term_to_string head21
                                    in
                                 let uu____13119 = args_to_string args2  in
                                 FStar_Util.format4
                                   "unequal number of arguments: %s[%s] and %s[%s]"
                                   uu____13116 uu____13117 uu____13118
                                   uu____13119
                                  in
                               giveup env1 uu____13115 orig
                             else
                               (let uu____13121 =
                                  (nargs = (Prims.parse_int "0")) ||
                                    (let uu____13127 =
                                       FStar_Syntax_Util.eq_args args1 args2
                                        in
                                     uu____13127 = FStar_Syntax_Util.Equal)
                                   in
                                if uu____13121
                                then
                                  let uu____13128 =
                                    solve_maybe_uinsts env1 orig head11
                                      head21 wl1
                                     in
                                  match uu____13128 with
                                  | USolved wl2 ->
                                      let uu____13130 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____13130
                                  | UFailed msg -> giveup env1 msg orig
                                  | UDeferred wl2 ->
                                      solve env1
                                        (defer "universe constraints" orig
                                           wl2)
                                else
                                  (let uu____13134 =
                                     base_and_refinement env1 t1  in
                                   match uu____13134 with
                                   | (base1,refinement1) ->
                                       let uu____13159 =
                                         base_and_refinement env1 t2  in
                                       (match uu____13159 with
                                        | (base2,refinement2) ->
                                            (match (refinement1, refinement2)
                                             with
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.None
                                                ) ->
                                                 let uu____13216 =
                                                   solve_maybe_uinsts env1
                                                     orig head11 head21 wl1
                                                    in
                                                 (match uu____13216 with
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
                                                          (fun uu____13238 
                                                             ->
                                                             fun uu____13239 
                                                               ->
                                                               match 
                                                                 (uu____13238,
                                                                   uu____13239)
                                                               with
                                                               | ((a,uu____13257),
                                                                  (a',uu____13259))
                                                                   ->
                                                                   let uu____13268
                                                                    =
                                                                    let uu____13273
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____13273
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
                                                                    uu____13268)
                                                          args1 args2
                                                         in
                                                      let formula =
                                                        let uu____13279 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               FStar_Pervasives_Native.fst
                                                                 (p_guard p))
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____13279
                                                         in
                                                      let wl3 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl2
                                                         in
                                                      solve env1
                                                        (attempt subprobs wl3))
                                             | uu____13285 ->
                                                 let lhs =
                                                   force_refinement
                                                     (base1, refinement1)
                                                    in
                                                 let rhs =
                                                   force_refinement
                                                     (base2, refinement2)
                                                    in
                                                 solve_t env1
                                                   (let uu___149_13321 =
                                                      problem  in
                                                    {
                                                      FStar_TypeChecker_Common.pid
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.pid);
                                                      FStar_TypeChecker_Common.lhs
                                                        = lhs;
                                                      FStar_TypeChecker_Common.relation
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.relation);
                                                      FStar_TypeChecker_Common.rhs
                                                        = rhs;
                                                      FStar_TypeChecker_Common.element
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.element);
                                                      FStar_TypeChecker_Common.logical_guard
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.logical_guard);
                                                      FStar_TypeChecker_Common.scope
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.scope);
                                                      FStar_TypeChecker_Common.reason
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.reason);
                                                      FStar_TypeChecker_Common.loc
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.loc);
                                                      FStar_TypeChecker_Common.rank
                                                        =
                                                        (uu___149_13321.FStar_TypeChecker_Common.rank)
                                                    }) wl1)))))))
           in
        let force_quasi_pattern xs_opt uu____13356 =
          match uu____13356 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____13399 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13399 then f () else ()  in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                let uu____13498 =
                  debug1
                    (fun uu____13503  ->
                       let uu____13504 =
                         FStar_Syntax_Print.binders_to_string ", " pat_args
                          in
                       FStar_Util.print1 "pat_args so far: {%s}\n"
                         uu____13504)
                   in
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____13572  ->
                              match uu____13572 with
                              | (x,imp) ->
                                  let uu____13583 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  (uu____13583, imp)))
                       in
                    let pattern_vars1 = FStar_List.rev pattern_vars  in
                    let kk =
                      let uu____13596 = FStar_Syntax_Util.type_u ()  in
                      match uu____13596 with
                      | (t1,uu____13602) ->
                          let uu____13603 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1
                             in
                          FStar_Pervasives_Native.fst uu____13603
                       in
                    let uu____13608 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk  in
                    (match uu____13608 with
                     | (t',tm_u1) ->
                         let uu____13621 = destruct_flex_t t'  in
                         (match uu____13621 with
                          | (uu____13658,u1,k1,uu____13661) ->
                              let all_formals = FStar_List.rev seen_formals
                                 in
                              let k2 =
                                let uu____13720 =
                                  FStar_Syntax_Syntax.mk_Total res_t  in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____13720
                                 in
                              let sol =
                                let uu____13724 =
                                  let uu____13733 = u_abs k2 all_formals t'
                                     in
                                  ((u, k2), uu____13733)  in
                                TERM uu____13724  in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos
                                 in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13861 =
                      debug1
                        (fun uu____13868  ->
                           let uu____13869 =
                             FStar_Syntax_Print.binder_to_string formal  in
                           let uu____13870 =
                             FStar_Syntax_Print.args_to_string [hd1]  in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____13869 uu____13870)
                       in
                    let uu____13883 = pat_var_opt env pat_args hd1  in
                    (match uu____13883 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____13900 =
                           debug1
                             (fun uu____13903  ->
                                FStar_Util.print_string "not a pattern var\n")
                            in
                         aux pat_args pat_args_set pattern_vars
                           pattern_var_set (formal :: seen_formals) formals1
                           res_t tl1
                     | FStar_Pervasives_Native.Some y ->
                         let maybe_pat =
                           match xs_opt with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some xs ->
                               FStar_All.pipe_right xs
                                 (FStar_Util.for_some
                                    (fun uu____13946  ->
                                       match uu____13946 with
                                       | (x,uu____13952) ->
                                           FStar_Syntax_Syntax.bv_eq x
                                             (FStar_Pervasives_Native.fst y)))
                            in
                         if Prims.op_Negation maybe_pat
                         then
                           aux pat_args pat_args_set pattern_vars
                             pattern_var_set (formal :: seen_formals)
                             formals1 res_t tl1
                         else
                           (let uu____13960 =
                              debug1
                                (fun uu____13967  ->
                                   let uu____13968 =
                                     FStar_Syntax_Print.args_to_string [hd1]
                                      in
                                   let uu____13981 =
                                     FStar_Syntax_Print.binder_to_string y
                                      in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13968
                                     uu____13981)
                               in
                            let fvs =
                              FStar_Syntax_Free.names
                                (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                               in
                            let uu____13985 =
                              let uu____13986 =
                                FStar_Util.set_is_subset_of fvs pat_args_set
                                 in
                              Prims.op_Negation uu____13986  in
                            if uu____13985
                            then
                              let uu____13993 =
                                debug1
                                  (fun uu____13998  ->
                                     let uu____13999 =
                                       let uu____14002 =
                                         FStar_Syntax_Print.args_to_string
                                           [hd1]
                                          in
                                       let uu____14015 =
                                         let uu____14018 =
                                           FStar_Syntax_Print.binder_to_string
                                             y
                                            in
                                         let uu____14019 =
                                           let uu____14022 =
                                             FStar_Syntax_Print.term_to_string
                                               (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                              in
                                           let uu____14023 =
                                             let uu____14026 =
                                               names_to_string fvs  in
                                             let uu____14027 =
                                               let uu____14030 =
                                                 names_to_string
                                                   pattern_var_set
                                                  in
                                               [uu____14030]  in
                                             uu____14026 :: uu____14027  in
                                           uu____14022 :: uu____14023  in
                                         uu____14018 :: uu____14019  in
                                       uu____14002 :: uu____14015  in
                                     FStar_Util.print
                                       "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                       uu____13999)
                                 in
                              aux pat_args pat_args_set pattern_vars
                                pattern_var_set (formal :: seen_formals)
                                formals1 res_t tl1
                            else
                              (let uu____14032 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst y)
                                   pat_args_set
                                  in
                               let uu____14035 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set
                                  in
                               aux (y :: pat_args) uu____14032 (formal ::
                                 pattern_vars) uu____14035 (formal ::
                                 seen_formals) formals1 res_t tl1)))
                | ([],uu____14042::uu____14043) ->
                    let uu____14074 =
                      let uu____14087 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t  in
                      FStar_Syntax_Util.arrow_formals uu____14087  in
                    (match uu____14074 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____14126 ->
                              aux pat_args pat_args_set pattern_vars
                                pattern_var_set seen_formals more_formals
                                res_t1 args1))
                | (uu____14133::uu____14134,[]) ->
                    FStar_Pervasives_Native.None
                 in
              let uu____14157 =
                let uu____14170 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k  in
                FStar_Syntax_Util.arrow_formals uu____14170  in
              (match uu____14157 with
               | (all_formals,res_t) ->
                   let uu____14195 =
                     debug1
                       (fun uu____14206  ->
                          let uu____14207 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____14208 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____14209 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____14210 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____14207 uu____14208 uu____14209 uu____14210)
                      in
                   let uu____14211 = FStar_Syntax_Syntax.new_bv_set ()  in
                   let uu____14214 = FStar_Syntax_Syntax.new_bv_set ()  in
                   aux [] uu____14211 [] uu____14214 [] all_formals res_t
                     args)
           in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____14254 = lhs  in
          match uu____14254 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____14264 ->
                    let uu____14265 = sn_binders env1 pat_vars1  in
                    u_abs k_uv uu____14265 rhs
                 in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1
                 in
              solve env1 wl2
           in
        let imitate orig env1 wl1 p =
          let uu____14292 = p  in
          match uu____14292 with
          | (((u,k),xs,c),ps,(h,uu____14303,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____14391 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____14391 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____14414 = h gs_xs  in
                     let uu____14415 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                        in
                     FStar_Syntax_Util.abs xs1 uu____14414 uu____14415  in
                   let uu____14420 =
                     let uu____14421 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____14421
                     then
                       let uu____14422 =
                         let uu____14425 =
                           let uu____14426 =
                             FStar_List.map tc_to_string gs_xs  in
                           FStar_All.pipe_right uu____14426
                             (FStar_String.concat "\n\t>")
                            in
                         let uu____14431 =
                           let uu____14434 =
                             FStar_Syntax_Print.binders_to_string ", " xs1
                              in
                           let uu____14435 =
                             let uu____14438 =
                               FStar_Syntax_Print.comp_to_string c  in
                             let uu____14439 =
                               let uu____14442 =
                                 FStar_Syntax_Print.term_to_string im  in
                               let uu____14443 =
                                 let uu____14446 =
                                   FStar_Syntax_Print.tag_of_term im  in
                                 let uu____14447 =
                                   let uu____14450 =
                                     let uu____14451 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs
                                        in
                                     FStar_All.pipe_right uu____14451
                                       (FStar_String.concat ", ")
                                      in
                                   let uu____14456 =
                                     let uu____14459 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula
                                        in
                                     [uu____14459]  in
                                   uu____14450 :: uu____14456  in
                                 uu____14446 :: uu____14447  in
                               uu____14442 :: uu____14443  in
                             uu____14438 :: uu____14439  in
                           uu____14434 :: uu____14435  in
                         uu____14425 :: uu____14431  in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____14422
                     else ()  in
                   let uu____14461 =
                     def_check_closed (p_loc orig) "imitate" im  in
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some formula)
                       [TERM ((u, k), im)] wl1
                      in
                   solve env1 (attempt sub_probs wl2))
           in
        let imitate' orig env1 wl1 uu___113_14485 =
          match uu___113_14485 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____14522 = p  in
          match uu____14522 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____14619 = FStar_List.nth ps i  in
              (match uu____14619 with
               | (pi,uu____14623) ->
                   let uu____14628 = FStar_List.nth xs i  in
                   (match uu____14628 with
                    | (xi,uu____14640) ->
                        let rec gs k =
                          let uu____14654 =
                            let uu____14667 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k
                               in
                            FStar_Syntax_Util.arrow_formals uu____14667  in
                          match uu____14654 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____14744)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____14757 = new_uvar r xs k_a  in
                                    (match uu____14757 with
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
                                         let uu____14779 = aux subst2 tl1  in
                                         (match uu____14779 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____14806 =
                                                let uu____14809 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____14809 :: gi_xs'  in
                                              let uu____14810 =
                                                let uu____14813 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____14813 :: gi_ps'  in
                                              (uu____14806, uu____14810)))
                                 in
                              aux [] bs
                           in
                        let uu____14818 =
                          let uu____14819 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____14819
                           in
                        if uu____14818
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____14823 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____14823 with
                           | (g_xs,uu____14835) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____14846 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____14847 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_35  ->
                                        FStar_Pervasives_Native.Some _0_35)
                                    in
                                 FStar_Syntax_Util.abs xs uu____14846
                                   uu____14847
                                  in
                               let sub1 =
                                 let uu____14853 =
                                   let uu____14858 = p_scope orig  in
                                   let uu____14859 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____14862 =
                                     let uu____14865 =
                                       FStar_List.map
                                         (fun uu____14880  ->
                                            match uu____14880 with
                                            | (uu____14889,uu____14890,y) ->
                                                y) qs
                                        in
                                     FStar_All.pipe_left h uu____14865  in
                                   mk_problem uu____14858 orig uu____14859
                                     (p_rel orig) uu____14862
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_36  ->
                                      FStar_TypeChecker_Common.TProb _0_36)
                                   uu____14853
                                  in
                               let uu____14904 =
                                 let uu____14905 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____14905
                                 then
                                   let uu____14906 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____14907 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14906 uu____14907
                                 else ()  in
                               let wl2 =
                                 let uu____14910 =
                                   let uu____14913 =
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       (p_guard sub1)
                                      in
                                   FStar_Pervasives_Native.Some uu____14913
                                    in
                                 solve_prob orig uu____14910 [TERM (u, proj)]
                                   wl1
                                  in
                               let uu____14922 =
                                 solve env1 (attempt [sub1] wl2)  in
                               FStar_All.pipe_left
                                 (fun _0_37  ->
                                    FStar_Pervasives_Native.Some _0_37)
                                 uu____14922)))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14958 = lhs  in
          match uu____14958 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14995 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____14995 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____15028 =
                        let uu____15077 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____15077)  in
                      FStar_Pervasives_Native.Some uu____15028
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k  in
                         let uu____15229 =
                           let uu____15236 =
                             let uu____15237 = FStar_Syntax_Subst.compress k1
                                in
                             uu____15237.FStar_Syntax_Syntax.n  in
                           (uu____15236, args)  in
                         match uu____15229 with
                         | (uu____15248,[]) ->
                             let uu____15251 =
                               let uu____15262 =
                                 FStar_Syntax_Syntax.mk_Total k1  in
                               ([], uu____15262)  in
                             FStar_Pervasives_Native.Some uu____15251
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____15283,uu____15284) ->
                             let uu____15305 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____15305 with
                              | (uv1,uv_args) ->
                                  let uu____15348 =
                                    let uu____15349 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____15349.FStar_Syntax_Syntax.n  in
                                  (match uu____15348 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____15359) ->
                                       let uu____15384 =
                                         pat_vars env [] uv_args  in
                                       (match uu____15384 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____15411  ->
                                                      let uu____15412 =
                                                        let uu____15413 =
                                                          let uu____15414 =
                                                            let uu____15419 =
                                                              let uu____15420
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____15420
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____15419
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____15414
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____15413
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____15412))
                                               in
                                            let c1 =
                                              let uu____15430 =
                                                let uu____15431 =
                                                  let uu____15436 =
                                                    let uu____15437 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15437
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____15436
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____15431
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____15430
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____15450 =
                                                let uu____15453 =
                                                  let uu____15454 =
                                                    let uu____15457 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15457
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____15454
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15453
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____15450
                                               in
                                            let uu____15466 =
                                              def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol
                                               in
                                            let uu____15467 =
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol
                                               in
                                            FStar_Pervasives_Native.Some
                                              (xs1, c1))
                                   | uu____15476 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____15481,uu____15482) ->
                             let uu____15501 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____15501 with
                              | (uv1,uv_args) ->
                                  let uu____15544 =
                                    let uu____15545 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____15545.FStar_Syntax_Syntax.n  in
                                  (match uu____15544 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____15555) ->
                                       let uu____15580 =
                                         pat_vars env [] uv_args  in
                                       (match uu____15580 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____15607  ->
                                                      let uu____15608 =
                                                        let uu____15609 =
                                                          let uu____15610 =
                                                            let uu____15615 =
                                                              let uu____15616
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____15616
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____15615
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____15610
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____15609
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____15608))
                                               in
                                            let c1 =
                                              let uu____15626 =
                                                let uu____15627 =
                                                  let uu____15632 =
                                                    let uu____15633 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15633
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____15632
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____15627
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____15626
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____15646 =
                                                let uu____15649 =
                                                  let uu____15650 =
                                                    let uu____15653 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15653
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____15650
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15649
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____15646
                                               in
                                            let uu____15662 =
                                              def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol
                                               in
                                            let uu____15663 =
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol
                                               in
                                            FStar_Pervasives_Native.Some
                                              (xs1, c1))
                                   | uu____15672 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____15679) ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____15720 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____15720
                                 (fun _0_38  ->
                                    FStar_Pervasives_Native.Some _0_38)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____15756 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____15756 with
                                  | (args1,rest) ->
                                      let uu____15785 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____15785 with
                                       | (xs2,c2) ->
                                           let uu____15798 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____15798
                                             (fun uu____15822  ->
                                                match uu____15822 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15862 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____15862 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____15930 =
                                        let uu____15935 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15935
                                         in
                                      FStar_All.pipe_right uu____15930
                                        (fun _0_39  ->
                                           FStar_Pervasives_Native.Some _0_39))
                         | uu____15950 ->
                             let uu____15957 =
                               let uu____15962 =
                                 let uu____15963 =
                                   FStar_Syntax_Print.uvar_to_string uv  in
                                 let uu____15964 =
                                   FStar_Syntax_Print.term_to_string k1  in
                                 let uu____15965 =
                                   FStar_Syntax_Print.term_to_string k_uv  in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15963 uu____15964 uu____15965
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____15962)  in
                             FStar_Errors.raise_error uu____15957
                               t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15972 = elim k_uv ps  in
                       FStar_Util.bind_opt uu____15972
                         (fun uu____16029  ->
                            match uu____16029 with
                            | (xs1,c1) ->
                                let uu____16080 =
                                  let uu____16123 = decompose env t2  in
                                  (((uv, k_uv), xs1, c1), ps, uu____16123)
                                   in
                                FStar_Pervasives_Native.Some uu____16080))
                 in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail1 uu____16255 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                   in
                let rec try_project st i =
                  if i >= n1
                  then fail1 ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                     let uu____16271 = project orig env wl1 i st  in
                     match uu____16271 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16278 = FStar_Syntax_Unionfind.rollback tx
                            in
                         try_project st (i + (Prims.parse_int "1"))
                     | FStar_Pervasives_Native.Some (Failed uu____16285) ->
                         let uu____16290 = FStar_Syntax_Unionfind.rollback tx
                            in
                         try_project st (i + (Prims.parse_int "1"))
                     | FStar_Pervasives_Native.Some sol -> sol)
                   in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt  in
                  let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                  let uu____16300 = imitate orig env wl1 st  in
                  match uu____16300 with
                  | Failed uu____16305 ->
                      let uu____16310 = FStar_Syntax_Unionfind.rollback tx
                         in
                      try_project st (Prims.parse_int "0")
                  | sol -> sol
                else fail1 ()  in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____16340 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                match uu____16340 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____16363 = forced_lhs_pattern  in
                    (match uu____16363 with
                     | (lhs_t,uu____16365,uu____16366,uu____16367) ->
                         let uu____16368 =
                           let uu____16369 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16369
                           then
                             let uu____16370 = lhs1  in
                             match uu____16370 with
                             | (t0,uu____16372,uu____16373,uu____16374) ->
                                 let uu____16375 = forced_lhs_pattern  in
                                 (match uu____16375 with
                                  | (t11,uu____16377,uu____16378,uu____16379)
                                      ->
                                      let uu____16380 =
                                        FStar_Syntax_Print.term_to_string t0
                                         in
                                      let uu____16381 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____16380 uu____16381)
                           else ()  in
                         let rhs_vars = FStar_Syntax_Free.names rhs  in
                         let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                         let uu____16389 =
                           FStar_Util.set_is_subset_of rhs_vars lhs_vars  in
                         if uu____16389
                         then
                           let uu____16390 =
                             let uu____16391 =
                               FStar_TypeChecker_Env.debug env
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____16391
                             then
                               let uu____16392 =
                                 FStar_Syntax_Print.term_to_string rhs  in
                               let uu____16393 = names_to_string rhs_vars  in
                               let uu____16394 = names_to_string lhs_vars  in
                               FStar_Util.print3
                                 "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                 uu____16392 uu____16393 uu____16394
                             else ()  in
                           let tx = FStar_Syntax_Unionfind.new_transaction ()
                              in
                           let wl2 = extend_solution (p_pid orig) [sol] wl1
                              in
                           let uu____16398 =
                             let uu____16399 =
                               FStar_TypeChecker_Common.as_tprob orig  in
                             solve_t env uu____16399 wl2  in
                           (match uu____16398 with
                            | Failed uu____16400 ->
                                let uu____16405 =
                                  FStar_Syntax_Unionfind.rollback tx  in
                                imitate_or_project n1 lhs1 rhs stopt
                            | sol1 -> sol1)
                         else
                           (let uu____16408 =
                              let uu____16409 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____16409
                              then
                                FStar_Util.print_string
                                  "fvar check failed for quasi pattern ... im/proj\n"
                              else ()  in
                            imitate_or_project n1 lhs1 rhs stopt))
                 in
              let check_head fvs1 t21 =
                let uu____16424 = FStar_Syntax_Util.head_and_args t21  in
                match uu____16424 with
                | (hd1,uu____16440) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____16461 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____16474 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____16475 -> true
                     | uu____16492 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____16496 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____16496
                         then true
                         else
                           (let uu____16498 =
                              let uu____16499 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____16499
                              then
                                let uu____16500 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____16500
                              else ()  in
                            false))
                 in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let lhs1 = (t11, uv, k_uv, args_lhs)  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____16520 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____16520 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____16533 =
                            let uu____16534 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____16534
                             in
                          giveup_or_defer1 orig uu____16533
                        else
                          (let uu____16536 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____16536
                           then
                             let uu____16537 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____16537
                              then
                                let uu____16538 = subterms args_lhs  in
                                imitate' orig env wl1 uu____16538
                              else
                                (let uu____16542 =
                                   let uu____16543 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____16543
                                   then
                                     let uu____16544 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____16545 = names_to_string fvs1
                                        in
                                     let uu____16546 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____16544 uu____16545 uu____16546
                                   else ()  in
                                 use_pattern_equality orig env wl1 lhs1 vars
                                   t21))
                           else
                             if
                               ((Prims.op_Negation patterns_only) &&
                                  wl1.defer_ok)
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                             then
                               solve env
                                 (defer
                                    "flex pattern/rigid: occurs or freevar check"
                                    orig wl1)
                             else
                               (let uu____16550 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____16550
                                then
                                  let uu____16551 =
                                    let uu____16552 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____16552
                                    then
                                      let uu____16553 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____16554 = names_to_string fvs1
                                         in
                                      let uu____16555 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____16553 uu____16554 uu____16555
                                    else ()  in
                                  let uu____16557 = subterms args_lhs  in
                                  imitate_or_project
                                    (FStar_List.length args_lhs) lhs1 t21
                                    uu____16557
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
                     (let uu____16568 =
                        let uu____16569 = FStar_Syntax_Free.names t1  in
                        check_head uu____16569 t2  in
                      if uu____16568
                      then
                        let n_args_lhs = FStar_List.length args_lhs  in
                        let uu____16579 =
                          let uu____16580 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____16580
                          then
                            let uu____16581 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____16582 =
                              FStar_Util.string_of_int n_args_lhs  in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____16581 uu____16582
                          else ()  in
                        let uu____16590 = subterms args_lhs  in
                        pattern_eq_imitate_or_project n_args_lhs
                          (FStar_Pervasives_Native.fst lhs) t2 uu____16590
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____16674 uu____16675 r =
               match (uu____16674, uu____16675) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____16873 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____16873
                   then
                     let uu____16874 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____16874
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      let uu____16897 =
                        let uu____16898 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____16898
                        then
                          let uu____16899 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____16900 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____16901 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____16902 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____16903 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16899 uu____16900 uu____16901 uu____16902
                            uu____16903
                        else ()  in
                      let subst_k k xs2 args =
                        let xs_len = FStar_List.length xs2  in
                        let args_len = FStar_List.length args  in
                        if xs_len = args_len
                        then
                          let uu____16966 =
                            FStar_Syntax_Util.subst_of_list xs2 args  in
                          FStar_Syntax_Subst.subst uu____16966 k
                        else
                          if args_len < xs_len
                          then
                            (let uu____16980 =
                               FStar_Util.first_N args_len xs2  in
                             match uu____16980 with
                             | (xs3,xs_rest) ->
                                 let k3 =
                                   let uu____17034 =
                                     FStar_Syntax_Syntax.mk_GTotal k  in
                                   FStar_Syntax_Util.arrow xs_rest
                                     uu____17034
                                    in
                                 let uu____17037 =
                                   FStar_Syntax_Util.subst_of_list xs3 args
                                    in
                                 FStar_Syntax_Subst.subst uu____17037 k3)
                          else
                            (let uu____17041 =
                               let uu____17042 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____17043 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   xs2
                                  in
                               let uu____17044 =
                                 FStar_Syntax_Print.args_to_string args  in
                               FStar_Util.format3
                                 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                 uu____17042 uu____17043 uu____17044
                                in
                             failwith uu____17041)
                         in
                      let uu____17045 =
                        let uu____17052 =
                          let uu____17065 =
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.Beta] env k1
                             in
                          FStar_Syntax_Util.arrow_formals uu____17065  in
                        match uu____17052 with
                        | (bs,k1') ->
                            let uu____17090 =
                              let uu____17103 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.Beta] env k2
                                 in
                              FStar_Syntax_Util.arrow_formals uu____17103  in
                            (match uu____17090 with
                             | (cs,k2') ->
                                 let k1'_xs = subst_k k1' bs args1  in
                                 let k2'_ys = subst_k k2' cs args2  in
                                 let sub_prob =
                                   let uu____17131 =
                                     let uu____17136 = p_scope orig  in
                                     mk_problem uu____17136 orig k1'_xs
                                       FStar_TypeChecker_Common.EQ k2'_ys
                                       FStar_Pervasives_Native.None
                                       "flex-flex kinding"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_40  ->
                                        FStar_TypeChecker_Common.TProb _0_40)
                                     uu____17131
                                    in
                                 let uu____17141 =
                                   let uu____17146 =
                                     let uu____17147 =
                                       FStar_Syntax_Subst.compress k1'  in
                                     uu____17147.FStar_Syntax_Syntax.n  in
                                   let uu____17150 =
                                     let uu____17151 =
                                       FStar_Syntax_Subst.compress k2'  in
                                     uu____17151.FStar_Syntax_Syntax.n  in
                                   (uu____17146, uu____17150)  in
                                 (match uu____17141 with
                                  | (FStar_Syntax_Syntax.Tm_type
                                     uu____17160,uu____17161) ->
                                      (k1'_xs, [sub_prob])
                                  | (uu____17164,FStar_Syntax_Syntax.Tm_type
                                     uu____17165) -> (k2'_ys, [sub_prob])
                                  | uu____17168 ->
                                      let uu____17173 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____17173 with
                                       | (t,uu____17185) ->
                                           let uu____17186 = new_uvar r zs t
                                              in
                                           (match uu____17186 with
                                            | (k_zs,uu____17198) ->
                                                let kprob =
                                                  let uu____17200 =
                                                    let uu____17205 =
                                                      p_scope orig  in
                                                    mk_problem uu____17205
                                                      orig k1'_xs
                                                      FStar_TypeChecker_Common.EQ
                                                      k_zs
                                                      FStar_Pervasives_Native.None
                                                      "flex-flex kinding"
                                                     in
                                                  FStar_All.pipe_left
                                                    (fun _0_41  ->
                                                       FStar_TypeChecker_Common.TProb
                                                         _0_41) uu____17200
                                                   in
                                                (k_zs, [sub_prob; kprob])))))
                         in
                      match uu____17045 with
                      | (k_u',sub_probs) ->
                          let uu____17218 =
                            let uu____17229 =
                              let uu____17230 = new_uvar r zs k_u'  in
                              FStar_All.pipe_left FStar_Pervasives_Native.fst
                                uu____17230
                               in
                            let uu____17239 =
                              let uu____17242 =
                                FStar_Syntax_Syntax.mk_Total k_u'  in
                              FStar_Syntax_Util.arrow xs1 uu____17242  in
                            let uu____17245 =
                              let uu____17248 =
                                FStar_Syntax_Syntax.mk_Total k_u'  in
                              FStar_Syntax_Util.arrow ys1 uu____17248  in
                            (uu____17229, uu____17239, uu____17245)  in
                          (match uu____17218 with
                           | (u_zs,knew1,knew2) ->
                               let sub1 = u_abs knew1 xs1 u_zs  in
                               let uu____17267 =
                                 occurs_check env wl1 (u1, k1) sub1  in
                               (match uu____17267 with
                                | (occurs_ok,msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      giveup_or_defer1 orig
                                        "flex-flex: failed occcurs check"
                                    else
                                      (let sol1 = TERM ((u1, k1), sub1)  in
                                       let uu____17286 =
                                         FStar_Syntax_Unionfind.equiv u1 u2
                                          in
                                       if uu____17286
                                       then
                                         let wl2 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None
                                             [sol1] wl1
                                            in
                                         solve env wl2
                                       else
                                         (let sub2 = u_abs knew2 ys1 u_zs  in
                                          let uu____17290 =
                                            occurs_check env wl1 (u2, k2)
                                              sub2
                                             in
                                          match uu____17290 with
                                          | (occurs_ok1,msg1) ->
                                              if Prims.op_Negation occurs_ok1
                                              then
                                                giveup_or_defer1 orig
                                                  "flex-flex: failed occurs check"
                                              else
                                                (let sol2 =
                                                   TERM ((u2, k2), sub2)  in
                                                 let wl2 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     [sol1; sol2] wl1
                                                    in
                                                 solve env
                                                   (attempt sub_probs wl2)))))))
                in
             let solve_one_pat uu____17345 uu____17346 =
               match (uu____17345, uu____17346) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   let uu____17463 =
                     let uu____17464 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17464
                     then
                       let uu____17465 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____17466 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____17465 uu____17466
                     else ()  in
                   let uu____17468 = FStar_Syntax_Unionfind.equiv u1 u2  in
                   if uu____17468
                   then
                     let sub_probs =
                       FStar_List.map2
                         (fun uu____17487  ->
                            fun uu____17488  ->
                              match (uu____17487, uu____17488) with
                              | ((a,uu____17506),(t21,uu____17508)) ->
                                  let uu____17517 =
                                    let uu____17522 = p_scope orig  in
                                    let uu____17523 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    mk_problem uu____17522 orig uu____17523
                                      FStar_TypeChecker_Common.EQ t21
                                      FStar_Pervasives_Native.None
                                      "flex-flex index"
                                     in
                                  FStar_All.pipe_right uu____17517
                                    (fun _0_42  ->
                                       FStar_TypeChecker_Common.TProb _0_42))
                         xs args2
                        in
                     let guard =
                       let uu____17529 =
                         FStar_List.map
                           (fun p  ->
                              FStar_All.pipe_right (p_guard p)
                                FStar_Pervasives_Native.fst) sub_probs
                          in
                       FStar_Syntax_Util.mk_conj_l uu____17529  in
                     let wl1 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl
                        in
                     solve env (attempt sub_probs wl1)
                   else
                     (let t21 = sn env t2  in
                      let rhs_vars = FStar_Syntax_Free.names t21  in
                      let uu____17544 = occurs_check env wl (u1, k1) t21  in
                      match uu____17544 with
                      | (occurs_ok,uu____17552) ->
                          let lhs_vars =
                            FStar_Syntax_Free.names_of_binders xs  in
                          let uu____17560 =
                            occurs_ok &&
                              (FStar_Util.set_is_subset_of rhs_vars lhs_vars)
                             in
                          if uu____17560
                          then
                            let sol =
                              let uu____17562 =
                                let uu____17571 = u_abs k1 xs t21  in
                                ((u1, k1), uu____17571)  in
                              TERM uu____17562  in
                            let wl1 =
                              solve_prob orig FStar_Pervasives_Native.None
                                [sol] wl
                               in
                            solve env wl1
                          else
                            (let uu____17578 =
                               occurs_ok &&
                                 (FStar_All.pipe_left Prims.op_Negation
                                    wl.defer_ok)
                                in
                             if uu____17578
                             then
                               let uu____17579 =
                                 force_quasi_pattern
                                   (FStar_Pervasives_Native.Some xs)
                                   (t21, u2, k2, args2)
                                  in
                               match uu____17579 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup_or_defer1 orig
                                     "flex-flex constraint"
                               | FStar_Pervasives_Native.Some
                                   (sol,(uu____17603,u21,k21,ys)) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   let uu____17628 =
                                     let uu____17629 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____17629
                                     then
                                       let uu____17630 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (2): %s\n"
                                         uu____17630
                                     else ()  in
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____17637 ->
                                        giveup env "impossible" orig)
                             else
                               giveup_or_defer1 orig "flex-flex constraint"))
                in
             let uu____17639 = lhs  in
             match uu____17639 with
             | (t1,u1,k1,args1) ->
                 let uu____17644 = rhs  in
                 (match uu____17644 with
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
                       | uu____17684 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____17694 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____17694 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____17712) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  let uu____17718 =
                                    let uu____17719 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____17719
                                    then
                                      let uu____17720 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____17720
                                    else ()  in
                                  (match orig with
                                   | FStar_TypeChecker_Common.TProb p ->
                                       solve_t env p wl1
                                   | uu____17727 ->
                                       giveup env "impossible" orig)))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____17729 = def_check_prob "solve_t'.2" orig  in
        let uu____17730 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____17730
        then
          let uu____17731 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____17731
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____17735 = FStar_Util.physical_equality t1 t2  in
           if uu____17735
           then
             let uu____17736 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____17736
           else
             (let uu____17738 =
                let uu____17739 =
                  FStar_TypeChecker_Env.debug env
                    (FStar_Options.Other "RelCheck")
                   in
                if uu____17739
                then
                  let uu____17740 =
                    FStar_Util.string_of_int
                      problem.FStar_TypeChecker_Common.pid
                     in
                  let uu____17741 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____17742 = FStar_Syntax_Print.tag_of_term t2  in
                  FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17740
                    uu____17741 uu____17742
                else ()  in
              let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____17745,uu____17746) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____17771,FStar_Syntax_Syntax.Tm_delayed uu____17772) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____17797,uu____17798) ->
                  let uu____17825 =
                    let uu___150_17826 = problem  in
                    let uu____17827 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___150_17826.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17827;
                      FStar_TypeChecker_Common.relation =
                        (uu___150_17826.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___150_17826.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___150_17826.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___150_17826.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.scope =
                        (uu___150_17826.FStar_TypeChecker_Common.scope);
                      FStar_TypeChecker_Common.reason =
                        (uu___150_17826.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___150_17826.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___150_17826.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17825 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____17828,uu____17829) ->
                  let uu____17836 =
                    let uu___151_17837 = problem  in
                    let uu____17838 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___151_17837.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17838;
                      FStar_TypeChecker_Common.relation =
                        (uu___151_17837.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___151_17837.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___151_17837.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___151_17837.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.scope =
                        (uu___151_17837.FStar_TypeChecker_Common.scope);
                      FStar_TypeChecker_Common.reason =
                        (uu___151_17837.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___151_17837.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___151_17837.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17836 wl
              | (uu____17839,FStar_Syntax_Syntax.Tm_ascribed uu____17840) ->
                  let uu____17867 =
                    let uu___152_17868 = problem  in
                    let uu____17869 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___152_17868.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___152_17868.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___152_17868.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17869;
                      FStar_TypeChecker_Common.element =
                        (uu___152_17868.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___152_17868.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.scope =
                        (uu___152_17868.FStar_TypeChecker_Common.scope);
                      FStar_TypeChecker_Common.reason =
                        (uu___152_17868.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___152_17868.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___152_17868.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17867 wl
              | (uu____17870,FStar_Syntax_Syntax.Tm_meta uu____17871) ->
                  let uu____17878 =
                    let uu___153_17879 = problem  in
                    let uu____17880 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___153_17879.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___153_17879.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___153_17879.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17880;
                      FStar_TypeChecker_Common.element =
                        (uu___153_17879.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___153_17879.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.scope =
                        (uu___153_17879.FStar_TypeChecker_Common.scope);
                      FStar_TypeChecker_Common.reason =
                        (uu___153_17879.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___153_17879.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___153_17879.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17878 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____17882),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____17884)) ->
                  let uu____17893 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____17893
              | (FStar_Syntax_Syntax.Tm_bvar uu____17894,uu____17895) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____17896,FStar_Syntax_Syntax.Tm_bvar uu____17897) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___114_17954 =
                    match uu___114_17954 with
                    | [] -> c
                    | bs ->
                        let uu____17976 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____17976
                     in
                  let uu____17985 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____17985 with
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
                                  let uu____18129 =
                                    FStar_Options.use_eq_at_higher_order ()
                                     in
                                  if uu____18129
                                  then FStar_TypeChecker_Common.EQ
                                  else
                                    problem.FStar_TypeChecker_Common.relation
                                   in
                                let uu____18131 =
                                  mk_problem scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"
                                   in
                                FStar_All.pipe_left
                                  (fun _0_43  ->
                                     FStar_TypeChecker_Common.CProb _0_43)
                                  uu____18131))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___115_18210 =
                    match uu___115_18210 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18244 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18244 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun scope  ->
                            fun env1  ->
                              fun subst1  ->
                                let uu____18382 =
                                  let uu____18387 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18388 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_problem scope orig uu____18387
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18388 FStar_Pervasives_Native.None
                                    "lambda co-domain"
                                   in
                                FStar_All.pipe_left
                                  (fun _0_44  ->
                                     FStar_TypeChecker_Common.TProb _0_44)
                                  uu____18382))
              | (FStar_Syntax_Syntax.Tm_abs uu____18393,uu____18394) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18420 -> true
                    | uu____18437 -> false  in
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
                      (let uu____18486 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___154_18494 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___154_18494.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___154_18494.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___154_18494.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___154_18494.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___154_18494.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___154_18494.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___154_18494.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___154_18494.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___154_18494.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___154_18494.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___154_18494.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___154_18494.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___154_18494.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___154_18494.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___154_18494.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___154_18494.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___154_18494.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___154_18494.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___154_18494.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___154_18494.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___154_18494.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___154_18494.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___154_18494.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___154_18494.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___154_18494.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___154_18494.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___154_18494.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___154_18494.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___154_18494.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___154_18494.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___154_18494.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___154_18494.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___154_18494.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___154_18494.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____18486 with
                       | (uu____18497,ty,uu____18499) ->
                           let uu____18500 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____18500)
                     in
                  let uu____18501 =
                    let uu____18518 = maybe_eta t1  in
                    let uu____18525 = maybe_eta t2  in
                    (uu____18518, uu____18525)  in
                  (match uu____18501 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___155_18567 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___155_18567.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___155_18567.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___155_18567.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___155_18567.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___155_18567.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___155_18567.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___155_18567.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___155_18567.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18590 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18590
                       then
                         let uu____18591 = destruct_flex_pattern env not_abs
                            in
                         solve_t_flex_rigid true orig uu____18591 t_abs wl
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___156_18606 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___156_18606.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___156_18606.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___156_18606.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___156_18606.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___156_18606.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___156_18606.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___156_18606.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___156_18606.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18630 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18630
                       then
                         let uu____18631 = destruct_flex_pattern env not_abs
                            in
                         solve_t_flex_rigid true orig uu____18631 t_abs wl
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___156_18646 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___156_18646.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___156_18646.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___156_18646.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___156_18646.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___156_18646.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___156_18646.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___156_18646.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___156_18646.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____18650 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____18667,FStar_Syntax_Syntax.Tm_abs uu____18668) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18694 -> true
                    | uu____18711 -> false  in
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
                      (let uu____18760 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___154_18768 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___154_18768.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___154_18768.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___154_18768.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___154_18768.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___154_18768.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___154_18768.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___154_18768.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___154_18768.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___154_18768.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___154_18768.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___154_18768.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___154_18768.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___154_18768.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___154_18768.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___154_18768.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___154_18768.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___154_18768.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___154_18768.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___154_18768.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___154_18768.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___154_18768.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___154_18768.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___154_18768.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___154_18768.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___154_18768.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___154_18768.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___154_18768.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___154_18768.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___154_18768.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___154_18768.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___154_18768.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___154_18768.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___154_18768.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___154_18768.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____18760 with
                       | (uu____18771,ty,uu____18773) ->
                           let uu____18774 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____18774)
                     in
                  let uu____18775 =
                    let uu____18792 = maybe_eta t1  in
                    let uu____18799 = maybe_eta t2  in
                    (uu____18792, uu____18799)  in
                  (match uu____18775 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___155_18841 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___155_18841.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___155_18841.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___155_18841.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___155_18841.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___155_18841.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___155_18841.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___155_18841.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___155_18841.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18864 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18864
                       then
                         let uu____18865 = destruct_flex_pattern env not_abs
                            in
                         solve_t_flex_rigid true orig uu____18865 t_abs wl
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___156_18880 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___156_18880.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___156_18880.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___156_18880.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___156_18880.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___156_18880.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___156_18880.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___156_18880.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___156_18880.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18904 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18904
                       then
                         let uu____18905 = destruct_flex_pattern env not_abs
                            in
                         solve_t_flex_rigid true orig uu____18905 t_abs wl
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___156_18920 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___156_18920.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___156_18920.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___156_18920.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___156_18920.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___156_18920.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___156_18920.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___156_18920.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___156_18920.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____18924 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____18956 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____18956) &&
                       (let uu____18968 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____18968))
                      &&
                      (let uu____18983 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____18983 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___116_18994 =
                             match uu___116_18994 with
                             | FStar_Syntax_Syntax.Delta_constant  -> true
                             | FStar_Syntax_Syntax.Delta_defined_at_level
                                 uu____18995 -> true
                             | uu____18996 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____18997 -> false)
                     in
                  let uu____18998 = as_refinement should_delta env wl t1  in
                  (match uu____18998 with
                   | (x11,phi1) ->
                       let uu____19005 = as_refinement should_delta env wl t2
                          in
                       (match uu____19005 with
                        | (x21,phi21) ->
                            let base_prob =
                              let uu____19013 =
                                let uu____19018 = p_scope orig  in
                                mk_problem uu____19018 orig
                                  x11.FStar_Syntax_Syntax.sort
                                  problem.FStar_TypeChecker_Common.relation
                                  x21.FStar_Syntax_Syntax.sort
                                  problem.FStar_TypeChecker_Common.element
                                  "refinement base type"
                                 in
                              FStar_All.pipe_left
                                (fun _0_45  ->
                                   FStar_TypeChecker_Common.TProb _0_45)
                                uu____19013
                               in
                            let x12 = FStar_Syntax_Syntax.freshen_bv x11  in
                            let subst1 =
                              [FStar_Syntax_Syntax.DB
                                 ((Prims.parse_int "0"), x12)]
                               in
                            let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                               in
                            let phi22 = FStar_Syntax_Subst.subst subst1 phi21
                               in
                            let env1 = FStar_TypeChecker_Env.push_bv env x12
                               in
                            let mk_imp1 imp phi12 phi23 =
                              let uu____19055 = imp phi12 phi23  in
                              FStar_All.pipe_right uu____19055
                                (guard_on_element wl problem x12)
                               in
                            let fallback uu____19060 =
                              let impl =
                                if
                                  problem.FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ
                                then
                                  mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                    phi22
                                else
                                  mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                    phi22
                                 in
                              let guard =
                                let uu____19066 =
                                  FStar_All.pipe_right (p_guard base_prob)
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_Syntax_Util.mk_conj uu____19066 impl
                                 in
                              let wl1 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl
                                 in
                              solve env1 (attempt [base_prob] wl1)  in
                            if
                              problem.FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ
                            then
                              let ref_prob =
                                let uu____19075 =
                                  let uu____19080 =
                                    let uu____19081 = p_scope orig  in
                                    let uu____19088 =
                                      let uu____19095 =
                                        FStar_Syntax_Syntax.mk_binder x12  in
                                      [uu____19095]  in
                                    FStar_List.append uu____19081 uu____19088
                                     in
                                  mk_problem uu____19080 orig phi11
                                    FStar_TypeChecker_Common.EQ phi22
                                    FStar_Pervasives_Native.None
                                    "refinement formula"
                                   in
                                FStar_All.pipe_left
                                  (fun _0_46  ->
                                     FStar_TypeChecker_Common.TProb _0_46)
                                  uu____19075
                                 in
                              let uu____19104 =
                                solve env1
                                  (let uu___157_19106 = wl  in
                                   {
                                     attempting = [ref_prob];
                                     wl_deferred = [];
                                     ctr = (uu___157_19106.ctr);
                                     defer_ok = false;
                                     smt_ok = (uu___157_19106.smt_ok);
                                     tcenv = (uu___157_19106.tcenv)
                                   })
                                 in
                              (match uu____19104 with
                               | Failed uu____19113 -> fallback ()
                               | Success uu____19118 ->
                                   let guard =
                                     let uu____19122 =
                                       FStar_All.pipe_right
                                         (p_guard base_prob)
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____19127 =
                                       let uu____19128 =
                                         FStar_All.pipe_right
                                           (p_guard ref_prob)
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____19128
                                         (guard_on_element wl problem x12)
                                        in
                                     FStar_Syntax_Util.mk_conj uu____19122
                                       uu____19127
                                      in
                                   let wl1 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some guard)
                                       [] wl
                                      in
                                   let wl2 =
                                     let uu___158_19137 = wl1  in
                                     {
                                       attempting =
                                         (uu___158_19137.attempting);
                                       wl_deferred =
                                         (uu___158_19137.wl_deferred);
                                       ctr =
                                         (wl1.ctr + (Prims.parse_int "1"));
                                       defer_ok = (uu___158_19137.defer_ok);
                                       smt_ok = (uu___158_19137.smt_ok);
                                       tcenv = (uu___158_19137.tcenv)
                                     }  in
                                   solve env1 (attempt [base_prob] wl2))
                            else fallback ()))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19139,FStar_Syntax_Syntax.Tm_uvar uu____19140) ->
                  let uu____19173 = destruct_flex_t t1  in
                  let uu____19174 = destruct_flex_t t2  in
                  flex_flex1 orig uu____19173 uu____19174
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19175;
                    FStar_Syntax_Syntax.pos = uu____19176;
                    FStar_Syntax_Syntax.vars = uu____19177;_},uu____19178),FStar_Syntax_Syntax.Tm_uvar
                 uu____19179) ->
                  let uu____19232 = destruct_flex_t t1  in
                  let uu____19233 = destruct_flex_t t2  in
                  flex_flex1 orig uu____19232 uu____19233
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19234,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19235;
                    FStar_Syntax_Syntax.pos = uu____19236;
                    FStar_Syntax_Syntax.vars = uu____19237;_},uu____19238))
                  ->
                  let uu____19291 = destruct_flex_t t1  in
                  let uu____19292 = destruct_flex_t t2  in
                  flex_flex1 orig uu____19291 uu____19292
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19293;
                    FStar_Syntax_Syntax.pos = uu____19294;
                    FStar_Syntax_Syntax.vars = uu____19295;_},uu____19296),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19297;
                    FStar_Syntax_Syntax.pos = uu____19298;
                    FStar_Syntax_Syntax.vars = uu____19299;_},uu____19300))
                  ->
                  let uu____19373 = destruct_flex_t t1  in
                  let uu____19374 = destruct_flex_t t2  in
                  flex_flex1 orig uu____19373 uu____19374
              | (FStar_Syntax_Syntax.Tm_uvar uu____19375,uu____19376) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____19393 = destruct_flex_pattern env t1  in
                  solve_t_flex_rigid false orig uu____19393 t2 wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19400;
                    FStar_Syntax_Syntax.pos = uu____19401;
                    FStar_Syntax_Syntax.vars = uu____19402;_},uu____19403),uu____19404)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____19441 = destruct_flex_pattern env t1  in
                  solve_t_flex_rigid false orig uu____19441 t2 wl
              | (uu____19448,FStar_Syntax_Syntax.Tm_uvar uu____19449) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____19466,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19467;
                    FStar_Syntax_Syntax.pos = uu____19468;
                    FStar_Syntax_Syntax.vars = uu____19469;_},uu____19470))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19507,FStar_Syntax_Syntax.Tm_type uu____19508) ->
                  solve_t' env
                    (let uu___159_19526 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___159_19526.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___159_19526.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___159_19526.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___159_19526.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___159_19526.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___159_19526.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___159_19526.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___159_19526.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___159_19526.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19527;
                    FStar_Syntax_Syntax.pos = uu____19528;
                    FStar_Syntax_Syntax.vars = uu____19529;_},uu____19530),FStar_Syntax_Syntax.Tm_type
                 uu____19531) ->
                  solve_t' env
                    (let uu___159_19569 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___159_19569.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___159_19569.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___159_19569.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___159_19569.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___159_19569.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___159_19569.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___159_19569.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___159_19569.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___159_19569.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19570,FStar_Syntax_Syntax.Tm_arrow uu____19571) ->
                  solve_t' env
                    (let uu___159_19601 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___159_19601.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___159_19601.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___159_19601.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___159_19601.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___159_19601.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___159_19601.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___159_19601.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___159_19601.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___159_19601.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19602;
                    FStar_Syntax_Syntax.pos = uu____19603;
                    FStar_Syntax_Syntax.vars = uu____19604;_},uu____19605),FStar_Syntax_Syntax.Tm_arrow
                 uu____19606) ->
                  solve_t' env
                    (let uu___159_19656 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___159_19656.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___159_19656.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___159_19656.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___159_19656.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___159_19656.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___159_19656.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___159_19656.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___159_19656.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___159_19656.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____19657,uu____19658) ->
                  if wl.defer_ok
                  then
                    solve env (defer "flex-rigid subtyping deferred" orig wl)
                  else
                    (let new_rel = problem.FStar_TypeChecker_Common.relation
                        in
                     let uu____19677 =
                       let uu____19678 = is_top_level_prob orig  in
                       FStar_All.pipe_left Prims.op_Negation uu____19678  in
                     if uu____19677
                     then
                       let uu____19679 =
                         FStar_All.pipe_left
                           (fun _0_47  ->
                              FStar_TypeChecker_Common.TProb _0_47)
                           (let uu___160_19685 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___160_19685.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___160_19685.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation = new_rel;
                              FStar_TypeChecker_Common.rhs =
                                (uu___160_19685.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___160_19685.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___160_19685.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.scope =
                                (uu___160_19685.FStar_TypeChecker_Common.scope);
                              FStar_TypeChecker_Common.reason =
                                (uu___160_19685.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___160_19685.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___160_19685.FStar_TypeChecker_Common.rank)
                            })
                          in
                       let uu____19686 = destruct_flex_pattern env t1  in
                       solve_t_flex_rigid false uu____19679 uu____19686 t2 wl
                     else
                       (let uu____19694 = base_and_refinement env t2  in
                        match uu____19694 with
                        | (t_base,ref_opt) ->
                            (match ref_opt with
                             | FStar_Pervasives_Native.None  ->
                                 let uu____19723 =
                                   FStar_All.pipe_left
                                     (fun _0_48  ->
                                        FStar_TypeChecker_Common.TProb _0_48)
                                     (let uu___161_19729 = problem  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___161_19729.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___161_19729.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          new_rel;
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___161_19729.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___161_19729.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___161_19729.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___161_19729.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___161_19729.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___161_19729.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___161_19729.FStar_TypeChecker_Common.rank)
                                      })
                                    in
                                 let uu____19730 =
                                   destruct_flex_pattern env t1  in
                                 solve_t_flex_rigid false uu____19723
                                   uu____19730 t_base wl
                             | FStar_Pervasives_Native.Some (y,phi) ->
                                 let y' =
                                   let uu___162_19744 = y  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___162_19744.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___162_19744.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }  in
                                 let impl =
                                   guard_on_element wl problem y' phi  in
                                 let base_prob =
                                   let uu____19747 =
                                     mk_problem
                                       problem.FStar_TypeChecker_Common.scope
                                       orig t1 new_rel
                                       y.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "flex-rigid: base type"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_49  ->
                                        FStar_TypeChecker_Common.TProb _0_49)
                                     uu____19747
                                    in
                                 let guard =
                                   let uu____19759 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19759 impl
                                    in
                                 let wl1 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl
                                    in
                                 solve env (attempt [base_prob] wl1))))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19767;
                    FStar_Syntax_Syntax.pos = uu____19768;
                    FStar_Syntax_Syntax.vars = uu____19769;_},uu____19770),uu____19771)
                  ->
                  if wl.defer_ok
                  then
                    solve env (defer "flex-rigid subtyping deferred" orig wl)
                  else
                    (let new_rel = problem.FStar_TypeChecker_Common.relation
                        in
                     let uu____19810 =
                       let uu____19811 = is_top_level_prob orig  in
                       FStar_All.pipe_left Prims.op_Negation uu____19811  in
                     if uu____19810
                     then
                       let uu____19812 =
                         FStar_All.pipe_left
                           (fun _0_50  ->
                              FStar_TypeChecker_Common.TProb _0_50)
                           (let uu___160_19818 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___160_19818.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___160_19818.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation = new_rel;
                              FStar_TypeChecker_Common.rhs =
                                (uu___160_19818.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___160_19818.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___160_19818.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.scope =
                                (uu___160_19818.FStar_TypeChecker_Common.scope);
                              FStar_TypeChecker_Common.reason =
                                (uu___160_19818.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___160_19818.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___160_19818.FStar_TypeChecker_Common.rank)
                            })
                          in
                       let uu____19819 = destruct_flex_pattern env t1  in
                       solve_t_flex_rigid false uu____19812 uu____19819 t2 wl
                     else
                       (let uu____19827 = base_and_refinement env t2  in
                        match uu____19827 with
                        | (t_base,ref_opt) ->
                            (match ref_opt with
                             | FStar_Pervasives_Native.None  ->
                                 let uu____19856 =
                                   FStar_All.pipe_left
                                     (fun _0_51  ->
                                        FStar_TypeChecker_Common.TProb _0_51)
                                     (let uu___161_19862 = problem  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___161_19862.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___161_19862.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          new_rel;
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___161_19862.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___161_19862.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___161_19862.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___161_19862.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___161_19862.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___161_19862.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___161_19862.FStar_TypeChecker_Common.rank)
                                      })
                                    in
                                 let uu____19863 =
                                   destruct_flex_pattern env t1  in
                                 solve_t_flex_rigid false uu____19856
                                   uu____19863 t_base wl
                             | FStar_Pervasives_Native.Some (y,phi) ->
                                 let y' =
                                   let uu___162_19877 = y  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___162_19877.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___162_19877.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }  in
                                 let impl =
                                   guard_on_element wl problem y' phi  in
                                 let base_prob =
                                   let uu____19880 =
                                     mk_problem
                                       problem.FStar_TypeChecker_Common.scope
                                       orig t1 new_rel
                                       y.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "flex-rigid: base type"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_52  ->
                                        FStar_TypeChecker_Common.TProb _0_52)
                                     uu____19880
                                    in
                                 let guard =
                                   let uu____19892 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____19892 impl
                                    in
                                 let wl1 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl
                                    in
                                 solve env (attempt [base_prob] wl1))))
              | (uu____19900,FStar_Syntax_Syntax.Tm_uvar uu____19901) ->
                  if wl.defer_ok
                  then
                    solve env (defer "rigid-flex subtyping deferred" orig wl)
                  else
                    (let uu____19919 = base_and_refinement env t1  in
                     match uu____19919 with
                     | (t_base,uu____19931) ->
                         solve_t env
                           (let uu___163_19945 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___163_19945.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs = t_base;
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___163_19945.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___163_19945.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___163_19945.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.scope =
                                (uu___163_19945.FStar_TypeChecker_Common.scope);
                              FStar_TypeChecker_Common.reason =
                                (uu___163_19945.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___163_19945.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___163_19945.FStar_TypeChecker_Common.rank)
                            }) wl)
              | (uu____19946,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19947;
                    FStar_Syntax_Syntax.pos = uu____19948;
                    FStar_Syntax_Syntax.vars = uu____19949;_},uu____19950))
                  ->
                  if wl.defer_ok
                  then
                    solve env (defer "rigid-flex subtyping deferred" orig wl)
                  else
                    (let uu____19988 = base_and_refinement env t1  in
                     match uu____19988 with
                     | (t_base,uu____20000) ->
                         solve_t env
                           (let uu___163_20014 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___163_20014.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs = t_base;
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___163_20014.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___163_20014.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___163_20014.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.scope =
                                (uu___163_20014.FStar_TypeChecker_Common.scope);
                              FStar_TypeChecker_Common.reason =
                                (uu___163_20014.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___163_20014.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___163_20014.FStar_TypeChecker_Common.rank)
                            }) wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____20015,uu____20016) ->
                  let t21 =
                    let uu____20026 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20026  in
                  solve_t env
                    (let uu___164_20050 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_20050.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___164_20050.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___164_20050.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___164_20050.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_20050.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___164_20050.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_20050.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_20050.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_20050.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20051,FStar_Syntax_Syntax.Tm_refine uu____20052) ->
                  let t11 =
                    let uu____20062 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20062  in
                  solve_t env
                    (let uu___165_20086 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_20086.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___165_20086.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___165_20086.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___165_20086.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_20086.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___165_20086.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_20086.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_20086.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_20086.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let sc_prob =
                    let uu____20166 =
                      let uu____20171 = p_scope orig  in
                      mk_problem uu____20171 orig t11
                        FStar_TypeChecker_Common.EQ t21
                        FStar_Pervasives_Native.None "match scrutinee"
                       in
                    FStar_All.pipe_left
                      (fun _0_53  -> FStar_TypeChecker_Common.TProb _0_53)
                      uu____20166
                     in
                  let rec solve_branches brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20359 = br1  in
                        (match uu____20359 with
                         | (p1,w1,uu____20378) ->
                             let uu____20391 = br2  in
                             (match uu____20391 with
                              | (p2,w2,uu____20406) ->
                                  let uu____20411 =
                                    let uu____20412 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20412  in
                                  if uu____20411
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20420 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20420 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20463 = br2  in
                                         (match uu____20463 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20494 =
                                                  p_scope orig  in
                                                let uu____20501 =
                                                  let uu____20508 =
                                                    FStar_Syntax_Syntax.pat_bvs
                                                      p11
                                                     in
                                                  FStar_All.pipe_left
                                                    (FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder)
                                                    uu____20508
                                                   in
                                                FStar_List.append uu____20494
                                                  uu____20501
                                                 in
                                              let uu____20519 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____20534,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____20547) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      []
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____20580 =
                                                      let uu____20583 =
                                                        let uu____20584 =
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
                                                          uu____20584
                                                         in
                                                      [uu____20583]  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____20580
                                                 in
                                              FStar_Util.bind_opt uu____20519
                                                (fun wprobs  ->
                                                   let prob =
                                                     let uu____20608 =
                                                       mk_problem scope orig
                                                         e1
                                                         FStar_TypeChecker_Common.EQ
                                                         e21
                                                         FStar_Pervasives_Native.None
                                                         "branch body"
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_55  ->
                                                          FStar_TypeChecker_Common.TProb
                                                            _0_55)
                                                       uu____20608
                                                      in
                                                   let uu____20619 =
                                                     solve_branches rs1 rs2
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____20619
                                                     (fun r1  ->
                                                        FStar_Pervasives_Native.Some
                                                          (prob ::
                                                          (FStar_List.append
                                                             wprobs r1))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some []
                    | uu____20680 -> FStar_Pervasives_Native.None  in
                  let uu____20711 = solve_branches brs1 brs2  in
                  (match uu____20711 with
                   | FStar_Pervasives_Native.None  ->
                       giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some sub_probs ->
                       let sub_probs1 = sc_prob :: sub_probs  in
                       let wl1 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env (attempt sub_probs1 wl1))
              | (FStar_Syntax_Syntax.Tm_match uu____20727,uu____20728) ->
                  let head1 =
                    let uu____20754 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20754
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20798 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20798
                      FStar_Pervasives_Native.fst
                     in
                  let uu____20839 =
                    let uu____20840 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____20840
                    then
                      let uu____20841 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20842 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20843 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20841 uu____20842 uu____20843
                    else ()  in
                  let uu____20845 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____20845
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____20860 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____20860
                     then
                       let guard =
                         let uu____20872 =
                           let uu____20873 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____20873 = FStar_Syntax_Util.Equal  in
                         if uu____20872
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____20877 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_56  ->
                                 FStar_Pervasives_Native.Some _0_56)
                              uu____20877)
                          in
                       let uu____20880 = solve_prob orig guard [] wl  in
                       solve env uu____20880
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_uinst uu____20883,uu____20884) ->
                  let head1 =
                    let uu____20894 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20894
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20938 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20938
                      FStar_Pervasives_Native.fst
                     in
                  let uu____20979 =
                    let uu____20980 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____20980
                    then
                      let uu____20981 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20982 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20983 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20981 uu____20982 uu____20983
                    else ()  in
                  let uu____20985 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____20985
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21000 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21000
                     then
                       let guard =
                         let uu____21012 =
                           let uu____21013 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21013 = FStar_Syntax_Util.Equal  in
                         if uu____21012
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21017 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_57  ->
                                 FStar_Pervasives_Native.Some _0_57)
                              uu____21017)
                          in
                       let uu____21020 = solve_prob orig guard [] wl  in
                       solve env uu____21020
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_name uu____21023,uu____21024) ->
                  let head1 =
                    let uu____21028 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21028
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21072 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21072
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21113 =
                    let uu____21114 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21114
                    then
                      let uu____21115 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21116 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21117 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21115 uu____21116 uu____21117
                    else ()  in
                  let uu____21119 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21119
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21134 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21134
                     then
                       let guard =
                         let uu____21146 =
                           let uu____21147 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21147 = FStar_Syntax_Util.Equal  in
                         if uu____21146
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21151 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_58  ->
                                 FStar_Pervasives_Native.Some _0_58)
                              uu____21151)
                          in
                       let uu____21154 = solve_prob orig guard [] wl  in
                       solve env uu____21154
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_constant uu____21157,uu____21158) ->
                  let head1 =
                    let uu____21162 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21162
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21206 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21206
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21247 =
                    let uu____21248 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21248
                    then
                      let uu____21249 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21250 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21251 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21249 uu____21250 uu____21251
                    else ()  in
                  let uu____21253 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21253
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21268 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21268
                     then
                       let guard =
                         let uu____21280 =
                           let uu____21281 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21281 = FStar_Syntax_Util.Equal  in
                         if uu____21280
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21285 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              uu____21285)
                          in
                       let uu____21288 = solve_prob orig guard [] wl  in
                       solve env uu____21288
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_fvar uu____21291,uu____21292) ->
                  let head1 =
                    let uu____21296 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21296
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21340 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21340
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21381 =
                    let uu____21382 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21382
                    then
                      let uu____21383 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21384 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21385 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21383 uu____21384 uu____21385
                    else ()  in
                  let uu____21387 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21387
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21402 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21402
                     then
                       let guard =
                         let uu____21414 =
                           let uu____21415 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21415 = FStar_Syntax_Util.Equal  in
                         if uu____21414
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21419 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_60  ->
                                 FStar_Pervasives_Native.Some _0_60)
                              uu____21419)
                          in
                       let uu____21422 = solve_prob orig guard [] wl  in
                       solve env uu____21422
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_app uu____21425,uu____21426) ->
                  let head1 =
                    let uu____21444 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21444
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21488 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21488
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21529 =
                    let uu____21530 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21530
                    then
                      let uu____21531 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21532 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21533 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21531 uu____21532 uu____21533
                    else ()  in
                  let uu____21535 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21535
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21550 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21550
                     then
                       let guard =
                         let uu____21562 =
                           let uu____21563 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21563 = FStar_Syntax_Util.Equal  in
                         if uu____21562
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21567 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_61  ->
                                 FStar_Pervasives_Native.Some _0_61)
                              uu____21567)
                          in
                       let uu____21570 = solve_prob orig guard [] wl  in
                       solve env uu____21570
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____21573,FStar_Syntax_Syntax.Tm_match uu____21574) ->
                  let head1 =
                    let uu____21600 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21600
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21644 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21644
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21685 =
                    let uu____21686 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21686
                    then
                      let uu____21687 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21688 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21689 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21687 uu____21688 uu____21689
                    else ()  in
                  let uu____21691 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21691
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21706 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21706
                     then
                       let guard =
                         let uu____21718 =
                           let uu____21719 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21719 = FStar_Syntax_Util.Equal  in
                         if uu____21718
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21723 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              uu____21723)
                          in
                       let uu____21726 = solve_prob orig guard [] wl  in
                       solve env uu____21726
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____21729,FStar_Syntax_Syntax.Tm_uinst uu____21730) ->
                  let head1 =
                    let uu____21740 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21740
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21784 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21784
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21825 =
                    let uu____21826 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21826
                    then
                      let uu____21827 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21828 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21829 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21827 uu____21828 uu____21829
                    else ()  in
                  let uu____21831 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21831
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21846 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21846
                     then
                       let guard =
                         let uu____21858 =
                           let uu____21859 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21859 = FStar_Syntax_Util.Equal  in
                         if uu____21858
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21863 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              uu____21863)
                          in
                       let uu____21866 = solve_prob orig guard [] wl  in
                       solve env uu____21866
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____21869,FStar_Syntax_Syntax.Tm_name uu____21870) ->
                  let head1 =
                    let uu____21874 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21874
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21918 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21918
                      FStar_Pervasives_Native.fst
                     in
                  let uu____21959 =
                    let uu____21960 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____21960
                    then
                      let uu____21961 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21962 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21963 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21961 uu____21962 uu____21963
                    else ()  in
                  let uu____21965 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____21965
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____21980 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____21980
                     then
                       let guard =
                         let uu____21992 =
                           let uu____21993 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____21993 = FStar_Syntax_Util.Equal  in
                         if uu____21992
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____21997 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_64  ->
                                 FStar_Pervasives_Native.Some _0_64)
                              uu____21997)
                          in
                       let uu____22000 = solve_prob orig guard [] wl  in
                       solve env uu____22000
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____22003,FStar_Syntax_Syntax.Tm_constant uu____22004) ->
                  let head1 =
                    let uu____22008 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22008
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22052 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22052
                      FStar_Pervasives_Native.fst
                     in
                  let uu____22093 =
                    let uu____22094 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____22094
                    then
                      let uu____22095 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22096 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22097 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22095 uu____22096 uu____22097
                    else ()  in
                  let uu____22099 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____22099
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____22114 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____22114
                     then
                       let guard =
                         let uu____22126 =
                           let uu____22127 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____22127 = FStar_Syntax_Util.Equal  in
                         if uu____22126
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____22131 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_65  ->
                                 FStar_Pervasives_Native.Some _0_65)
                              uu____22131)
                          in
                       let uu____22134 = solve_prob orig guard [] wl  in
                       solve env uu____22134
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____22137,FStar_Syntax_Syntax.Tm_fvar uu____22138) ->
                  let head1 =
                    let uu____22142 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22142
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22186 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22186
                      FStar_Pervasives_Native.fst
                     in
                  let uu____22227 =
                    let uu____22228 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____22228
                    then
                      let uu____22229 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22230 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22231 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22229 uu____22230 uu____22231
                    else ()  in
                  let uu____22233 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____22233
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____22248 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____22248
                     then
                       let guard =
                         let uu____22260 =
                           let uu____22261 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____22261 = FStar_Syntax_Util.Equal  in
                         if uu____22260
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____22265 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_66  ->
                                 FStar_Pervasives_Native.Some _0_66)
                              uu____22265)
                          in
                       let uu____22268 = solve_prob orig guard [] wl  in
                       solve env uu____22268
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (uu____22271,FStar_Syntax_Syntax.Tm_app uu____22272) ->
                  let head1 =
                    let uu____22290 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22290
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22334 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22334
                      FStar_Pervasives_Native.fst
                     in
                  let uu____22375 =
                    let uu____22376 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____22376
                    then
                      let uu____22377 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22378 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22379 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22377 uu____22378 uu____22379
                    else ()  in
                  let uu____22381 =
                    (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                        (FStar_TypeChecker_Env.is_interpreted env head2))
                       && wl.smt_ok)
                      &&
                      (problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                     in
                  if uu____22381
                  then
                    let uv1 = FStar_Syntax_Free.uvars t1  in
                    let uv2 = FStar_Syntax_Free.uvars t2  in
                    let uu____22396 =
                      (FStar_Util.set_is_empty uv1) &&
                        (FStar_Util.set_is_empty uv2)
                       in
                    (if uu____22396
                     then
                       let guard =
                         let uu____22408 =
                           let uu____22409 = FStar_Syntax_Util.eq_tm t1 t2
                              in
                           uu____22409 = FStar_Syntax_Util.Equal  in
                         if uu____22408
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____22413 = mk_eq2 orig t1 t2  in
                            FStar_All.pipe_left
                              (fun _0_67  ->
                                 FStar_Pervasives_Native.Some _0_67)
                              uu____22413)
                          in
                       let uu____22416 = solve_prob orig guard [] wl  in
                       solve env uu____22416
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                  else rigid_rigid_delta env orig wl head1 head2 t1 t2
              | (FStar_Syntax_Syntax.Tm_let
                 uu____22419,FStar_Syntax_Syntax.Tm_let uu____22420) ->
                  let uu____22445 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____22445
                  then
                    let uu____22446 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____22446
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____22448,uu____22449) ->
                  let uu____22462 =
                    let uu____22467 =
                      let uu____22468 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____22469 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____22470 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____22471 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____22468 uu____22469 uu____22470 uu____22471
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____22467)
                     in
                  FStar_Errors.raise_error uu____22462
                    t1.FStar_Syntax_Syntax.pos
              | (uu____22472,FStar_Syntax_Syntax.Tm_let uu____22473) ->
                  let uu____22486 =
                    let uu____22491 =
                      let uu____22492 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____22493 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____22494 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____22495 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____22492 uu____22493 uu____22494 uu____22495
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____22491)
                     in
                  FStar_Errors.raise_error uu____22486
                    t1.FStar_Syntax_Syntax.pos
              | uu____22496 -> giveup env "head tag mismatch" orig))

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
          let uu____22528 = p_scope orig  in
          mk_problem uu____22528 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          let uu____22538 =
            let uu____22539 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "EQ")
               in
            if uu____22539
            then
              let uu____22540 =
                let uu____22541 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
                FStar_Syntax_Print.comp_to_string uu____22541  in
              let uu____22542 =
                let uu____22543 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
                FStar_Syntax_Print.comp_to_string uu____22543  in
              FStar_Util.print2
                "solve_c is using an equality constraint (%s vs %s)\n"
                uu____22540 uu____22542
            else ()  in
          let uu____22545 =
            let uu____22546 =
              FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                c2_comp.FStar_Syntax_Syntax.effect_name
               in
            Prims.op_Negation uu____22546  in
          if uu____22545
          then
            let uu____22547 =
              let uu____22548 =
                FStar_Syntax_Print.lid_to_string
                  c1_comp.FStar_Syntax_Syntax.effect_name
                 in
              let uu____22549 =
                FStar_Syntax_Print.lid_to_string
                  c2_comp.FStar_Syntax_Syntax.effect_name
                 in
              FStar_Util.format2 "incompatible effects: %s <> %s" uu____22548
                uu____22549
               in
            giveup env uu____22547 orig
          else
            (let ret_sub_prob =
               let uu____22552 =
                 sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                   FStar_TypeChecker_Common.EQ
                   c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                  in
               FStar_All.pipe_left
                 (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                 uu____22552
                in
             let arg_sub_probs =
               FStar_List.map2
                 (fun uu____22579  ->
                    fun uu____22580  ->
                      match (uu____22579, uu____22580) with
                      | ((a1,uu____22598),(a2,uu____22600)) ->
                          let uu____22609 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_69  ->
                               FStar_TypeChecker_Common.TProb _0_69)
                            uu____22609)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let sub_probs = ret_sub_prob :: arg_sub_probs  in
             let guard =
               let uu____22622 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____22622  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22650 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22657)::[] -> wp1
              | uu____22674 ->
                  let uu____22683 =
                    let uu____22684 =
                      let uu____22685 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____22685  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22684
                     in
                  failwith uu____22683
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____22693 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____22693]
              | x -> x  in
            let uu____22695 =
              let uu____22704 =
                let uu____22705 =
                  let uu____22706 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____22706 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____22705  in
              [uu____22704]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22695;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22707 = lift_c1 ()  in solve_eq uu____22707 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_22713  ->
                       match uu___117_22713 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22714 -> false))
                in
             let uu____22715 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____22749)::uu____22750,(wp2,uu____22752)::uu____22753)
                   -> (wp1, wp2)
               | uu____22810 ->
                   let uu____22831 =
                     let uu____22836 =
                       let uu____22837 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____22838 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____22837 uu____22838
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____22836)
                      in
                   FStar_Errors.raise_error uu____22831
                     env.FStar_TypeChecker_Env.range
                in
             match uu____22715 with
             | (wpc1,wpc2) ->
                 let uu____22857 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____22857
                 then
                   let uu____22860 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____22860 wl
                 else
                   (let uu____22864 =
                      let uu____22871 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____22871  in
                    match uu____22864 with
                    | (c2_decl,qualifiers) ->
                        let uu____22892 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____22892
                        then
                          let c1_repr =
                            let uu____22896 =
                              let uu____22897 =
                                let uu____22898 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____22898  in
                              let uu____22899 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22897 uu____22899
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22896
                             in
                          let c2_repr =
                            let uu____22901 =
                              let uu____22902 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____22903 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22902 uu____22903
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22901
                             in
                          let prob =
                            let uu____22905 =
                              let uu____22910 =
                                let uu____22911 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____22912 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____22911
                                  uu____22912
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____22910
                               in
                            FStar_TypeChecker_Common.TProb uu____22905  in
                          let wl1 =
                            let uu____22914 =
                              let uu____22917 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____22917  in
                            solve_prob orig uu____22914 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 (let uu____22925 =
                                    let uu____22926 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____22926
                                    then
                                      FStar_Util.print_string
                                        "Using trivial wp ... \n"
                                    else ()  in
                                  let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____22929 =
                                    let uu____22934 =
                                      let uu____22935 =
                                        let uu____22950 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c1_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.trivial
                                           in
                                        let uu____22951 =
                                          let uu____22954 =
                                            FStar_Syntax_Syntax.as_arg
                                              c11.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____22955 =
                                            let uu____22958 =
                                              let uu____22959 =
                                                (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                  c1_univ
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                  wpc1
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Syntax_Syntax.as_arg
                                                uu____22959
                                               in
                                            [uu____22958]  in
                                          uu____22954 :: uu____22955  in
                                        (uu____22950, uu____22951)  in
                                      FStar_Syntax_Syntax.Tm_app uu____22935
                                       in
                                    FStar_Syntax_Syntax.mk uu____22934  in
                                  uu____22929 FStar_Pervasives_Native.None r)
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____22968 =
                                    let uu____22973 =
                                      let uu____22974 =
                                        let uu____22989 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____22990 =
                                          let uu____22993 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____22994 =
                                            let uu____22997 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____22998 =
                                              let uu____23001 =
                                                let uu____23002 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23002
                                                 in
                                              [uu____23001]  in
                                            uu____22997 :: uu____22998  in
                                          uu____22993 :: uu____22994  in
                                        (uu____22989, uu____22990)  in
                                      FStar_Syntax_Syntax.Tm_app uu____22974
                                       in
                                    FStar_Syntax_Syntax.mk uu____22973  in
                                  uu____22968 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____23009 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____23009
                              in
                           let wl1 =
                             let uu____23019 =
                               let uu____23022 =
                                 let uu____23025 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____23025 g  in
                               FStar_All.pipe_left
                                 (fun _0_71  ->
                                    FStar_Pervasives_Native.Some _0_71)
                                 uu____23022
                                in
                             solve_prob orig uu____23019 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____23038 = FStar_Util.physical_equality c1 c2  in
        if uu____23038
        then
          let uu____23039 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____23039
        else
          (let uu____23041 =
             let uu____23042 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel")
                in
             if uu____23042
             then
               let uu____23043 = FStar_Syntax_Print.comp_to_string c1  in
               let uu____23044 = FStar_Syntax_Print.comp_to_string c2  in
               FStar_Util.print3 "solve_c %s %s %s\n" uu____23043
                 (rel_to_string problem.FStar_TypeChecker_Common.relation)
                 uu____23044
             else ()  in
           let uu____23046 =
             let uu____23051 =
               FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
             let uu____23052 =
               FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
             (uu____23051, uu____23052)  in
           match uu____23046 with
           | (c11,c21) ->
               (match ((c11.FStar_Syntax_Syntax.n),
                        (c21.FStar_Syntax_Syntax.n))
                with
                | (FStar_Syntax_Syntax.GTotal
                   (t1,uu____23056),FStar_Syntax_Syntax.Total
                   (t2,uu____23058)) when
                    FStar_Syntax_Util.non_informative t2 ->
                    let uu____23075 =
                      problem_using_guard orig t1
                        problem.FStar_TypeChecker_Common.relation t2
                        FStar_Pervasives_Native.None "result type"
                       in
                    solve_t env uu____23075 wl
                | (FStar_Syntax_Syntax.GTotal
                   uu____23078,FStar_Syntax_Syntax.Total uu____23079) ->
                    giveup env "incompatible monad ordering: GTot </: Tot"
                      orig
                | (FStar_Syntax_Syntax.Total
                   (t1,uu____23097),FStar_Syntax_Syntax.Total
                   (t2,uu____23099)) ->
                    let uu____23116 =
                      problem_using_guard orig t1
                        problem.FStar_TypeChecker_Common.relation t2
                        FStar_Pervasives_Native.None "result type"
                       in
                    solve_t env uu____23116 wl
                | (FStar_Syntax_Syntax.GTotal
                   (t1,uu____23120),FStar_Syntax_Syntax.GTotal
                   (t2,uu____23122)) ->
                    let uu____23139 =
                      problem_using_guard orig t1
                        problem.FStar_TypeChecker_Common.relation t2
                        FStar_Pervasives_Native.None "result type"
                       in
                    solve_t env uu____23139 wl
                | (FStar_Syntax_Syntax.Total
                   (t1,uu____23143),FStar_Syntax_Syntax.GTotal
                   (t2,uu____23145)) ->
                    let uu____23162 =
                      problem_using_guard orig t1
                        problem.FStar_TypeChecker_Common.relation t2
                        FStar_Pervasives_Native.None "result type"
                       in
                    solve_t env uu____23162 wl
                | (FStar_Syntax_Syntax.GTotal
                   uu____23165,FStar_Syntax_Syntax.Comp uu____23166) ->
                    let uu____23175 =
                      let uu___166_23180 = problem  in
                      let uu____23185 =
                        let uu____23186 =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                          uu____23186
                         in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___166_23180.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = uu____23185;
                        FStar_TypeChecker_Common.relation =
                          (uu___166_23180.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___166_23180.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___166_23180.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___166_23180.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___166_23180.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___166_23180.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___166_23180.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___166_23180.FStar_TypeChecker_Common.rank)
                      }  in
                    solve_c env uu____23175 wl
                | (FStar_Syntax_Syntax.Total
                   uu____23187,FStar_Syntax_Syntax.Comp uu____23188) ->
                    let uu____23197 =
                      let uu___166_23202 = problem  in
                      let uu____23207 =
                        let uu____23208 =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                          uu____23208
                         in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___166_23202.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = uu____23207;
                        FStar_TypeChecker_Common.relation =
                          (uu___166_23202.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___166_23202.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___166_23202.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___166_23202.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___166_23202.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___166_23202.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___166_23202.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___166_23202.FStar_TypeChecker_Common.rank)
                      }  in
                    solve_c env uu____23197 wl
                | (FStar_Syntax_Syntax.Comp
                   uu____23209,FStar_Syntax_Syntax.GTotal uu____23210) ->
                    let uu____23219 =
                      let uu___167_23224 = problem  in
                      let uu____23229 =
                        let uu____23230 =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                          uu____23230
                         in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_23224.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_23224.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___167_23224.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = uu____23229;
                        FStar_TypeChecker_Common.element =
                          (uu___167_23224.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_23224.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_23224.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_23224.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_23224.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_23224.FStar_TypeChecker_Common.rank)
                      }  in
                    solve_c env uu____23219 wl
                | (FStar_Syntax_Syntax.Comp
                   uu____23231,FStar_Syntax_Syntax.Total uu____23232) ->
                    let uu____23241 =
                      let uu___167_23246 = problem  in
                      let uu____23251 =
                        let uu____23252 =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                          uu____23252
                         in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_23246.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_23246.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___167_23246.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = uu____23251;
                        FStar_TypeChecker_Common.element =
                          (uu___167_23246.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_23246.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_23246.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_23246.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_23246.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_23246.FStar_TypeChecker_Common.rank)
                      }  in
                    solve_c env uu____23241 wl
                | (FStar_Syntax_Syntax.Comp
                   uu____23253,FStar_Syntax_Syntax.Comp uu____23254) ->
                    let uu____23255 =
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
                    if uu____23255
                    then
                      let uu____23256 =
                        problem_using_guard orig
                          (FStar_Syntax_Util.comp_result c11)
                          problem.FStar_TypeChecker_Common.relation
                          (FStar_Syntax_Util.comp_result c21)
                          FStar_Pervasives_Native.None "result type"
                         in
                      solve_t env uu____23256 wl
                    else
                      (let c1_comp =
                         FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                       let c2_comp =
                         FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                       if
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                       then
                         let uu____23262 =
                           let uu____23267 =
                             FStar_Ident.lid_equals
                               c1_comp.FStar_Syntax_Syntax.effect_name
                               c2_comp.FStar_Syntax_Syntax.effect_name
                              in
                           if uu____23267
                           then (c1_comp, c2_comp)
                           else
                             (let uu____23273 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let uu____23274 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              (uu____23273, uu____23274))
                            in
                         match uu____23262 with
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
                          let uu____23280 =
                            let uu____23281 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____23281
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ()  in
                          let uu____23283 =
                            FStar_TypeChecker_Env.monad_leq env
                              c12.FStar_Syntax_Syntax.effect_name
                              c22.FStar_Syntax_Syntax.effect_name
                             in
                          match uu____23283 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____23286 =
                                let uu____23287 =
                                  FStar_Syntax_Print.lid_to_string
                                    c12.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____23288 =
                                  FStar_Syntax_Print.lid_to_string
                                    c22.FStar_Syntax_Syntax.effect_name
                                   in
                                FStar_Util.format2
                                  "incompatible monad ordering: %s </: %s"
                                  uu____23287 uu____23288
                                 in
                              giveup env uu____23286 orig
                          | FStar_Pervasives_Native.Some edge ->
                              solve_sub c12 edge c22))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23295 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23333  ->
              match uu____23333 with
              | (uu____23346,uu____23347,u,uu____23349,uu____23350,uu____23351)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____23295 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____23384 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____23384 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____23402 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23430  ->
                match uu____23430 with
                | (u1,u2) ->
                    let uu____23437 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____23438 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____23437 uu____23438))
         in
      FStar_All.pipe_right uu____23402 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23459,[])) -> "{}"
      | uu____23484 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23501 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____23501
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23504 =
              FStar_List.map
                (fun uu____23514  ->
                   match uu____23514 with
                   | (uu____23519,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23504 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23524 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23524 imps
  
let new_t_problem :
  'Auu____23539 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____23539 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____23539)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____23579 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____23579
                then
                  let uu____23580 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____23581 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23580
                    (rel_to_string rel) uu____23581
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
            let uu____23613 =
              let uu____23616 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_72  -> FStar_Pervasives_Native.Some _0_72)
                uu____23616
               in
            FStar_Syntax_Syntax.new_bv uu____23613 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____23625 =
              let uu____23628 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_73  -> FStar_Pervasives_Native.Some _0_73)
                uu____23628
               in
            let uu____23631 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____23625 uu____23631  in
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
          let uu____23667 = FStar_Options.eager_inference ()  in
          if uu____23667
          then
            let uu___168_23668 = probs  in
            {
              attempting = (uu___168_23668.attempting);
              wl_deferred = (uu___168_23668.wl_deferred);
              ctr = (uu___168_23668.ctr);
              defer_ok = false;
              smt_ok = (uu___168_23668.smt_ok);
              tcenv = (uu___168_23668.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            let uu____23675 = FStar_Syntax_Unionfind.commit tx  in
            FStar_Pervasives_Native.Some deferred
        | Failed (d,s) ->
            let uu____23678 =
              let uu____23679 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____23679
              then
                let uu____23680 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____23680
              else ()  in
            let result = err (d, s)  in
            let uu____23685 = FStar_Syntax_Unionfind.rollback tx  in result
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu____23697 =
            let uu____23698 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23698
            then
              let uu____23699 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23699
            else ()  in
          let f1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.Eager_unfolding;
              FStar_TypeChecker_Normalize.Simplify;
              FStar_TypeChecker_Normalize.Primops;
              FStar_TypeChecker_Normalize.NoFullNorm] env f
             in
          let uu____23702 =
            let uu____23703 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23703
            then
              let uu____23704 = FStar_Syntax_Print.term_to_string f1  in
              FStar_Util.print1 "Simplified guard to %s\n" uu____23704
            else ()  in
          let f2 =
            let uu____23707 =
              let uu____23708 = FStar_Syntax_Util.unmeta f1  in
              uu____23708.FStar_Syntax_Syntax.n  in
            match uu____23707 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
                -> FStar_TypeChecker_Common.Trivial
            | uu____23712 -> FStar_TypeChecker_Common.NonTrivial f1  in
          let uu___169_23713 = g  in
          {
            FStar_TypeChecker_Env.guard_f = f2;
            FStar_TypeChecker_Env.deferred =
              (uu___169_23713.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___169_23713.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___169_23713.FStar_TypeChecker_Env.implicits)
          }
  
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
            let uu____23738 =
              let uu____23739 =
                let uu____23740 =
                  let uu____23741 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____23741
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____23740;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____23739  in
            FStar_All.pipe_left
              (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____23738
  
let with_guard_no_simp :
  'Auu____23772 .
    'Auu____23772 ->
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
            let uu____23795 =
              let uu____23796 =
                let uu____23797 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____23797
                  (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____23796;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____23795
  
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
          let uu____23842 =
            let uu____23843 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____23843
            then
              let uu____23844 = FStar_Syntax_Print.term_to_string t1  in
              let uu____23845 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print2 "try_teq of %s and %s\n" uu____23844
                uu____23845
            else ()  in
          let prob =
            let uu____23848 =
              let uu____23853 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                FStar_Pervasives_Native.None uu____23853
               in
            FStar_All.pipe_left
              (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
              uu____23848
             in
          let g =
            let uu____23861 =
              let uu____23864 = singleton' env prob smt_ok  in
              solve_and_commit env uu____23864
                (fun uu____23866  -> FStar_Pervasives_Native.None)
               in
            FStar_All.pipe_left (with_guard env prob) uu____23861  in
          g
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23890 = try_teq true env t1 t2  in
        match uu____23890 with
        | FStar_Pervasives_Native.None  ->
            let uu____23893 =
              let uu____23894 = FStar_TypeChecker_Env.get_range env  in
              let uu____23895 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____23894 uu____23895  in
            trivial_guard
        | FStar_Pervasives_Native.Some g ->
            let uu____23901 =
              let uu____23902 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____23902
              then
                let uu____23903 = FStar_Syntax_Print.term_to_string t1  in
                let uu____23904 = FStar_Syntax_Print.term_to_string t2  in
                let uu____23905 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____23903
                  uu____23904 uu____23905
              else ()  in
            g
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____23927 = FStar_TypeChecker_Env.get_range env  in
          let uu____23928 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____23927 uu____23928
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____23950 =
          let uu____23951 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Rel")
             in
          if uu____23951
          then
            let uu____23952 = FStar_Syntax_Print.comp_to_string c1  in
            let uu____23953 = FStar_Syntax_Print.comp_to_string c2  in
            FStar_Util.print2 "sub_comp of %s and %s\n" uu____23952
              uu____23953
          else ()  in
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        let prob =
          let uu____23958 =
            let uu____23963 = FStar_TypeChecker_Env.get_range env  in
            new_problem env c1 rel c2 FStar_Pervasives_Native.None
              uu____23963 "sub_comp"
             in
          FStar_All.pipe_left
            (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____23958
           in
        let uu____23968 =
          let uu____23971 = singleton env prob  in
          solve_and_commit env uu____23971
            (fun uu____23973  -> FStar_Pervasives_Native.None)
           in
        FStar_All.pipe_left (with_guard env prob) uu____23968
  
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
      fun uu____24008  ->
        match uu____24008 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              let uu____24048 = FStar_Syntax_Unionfind.rollback tx  in
              let uu____24049 =
                let uu____24054 =
                  let uu____24055 = FStar_Syntax_Print.univ_to_string u1  in
                  let uu____24056 = FStar_Syntax_Print.univ_to_string u2  in
                  FStar_Util.format2 "Universe %s and %s are incompatible"
                    uu____24055 uu____24056
                   in
                (FStar_Errors.Fatal_IncompatibleUniverse, uu____24054)  in
              let uu____24057 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____24049 uu____24057  in
            let equiv1 v1 v' =
              let uu____24067 =
                let uu____24072 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____24073 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____24072, uu____24073)  in
              match uu____24067 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24092 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24122 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____24122 with
                      | FStar_Syntax_Syntax.U_unif uu____24129 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24158  ->
                                    match uu____24158 with
                                    | (u,v') ->
                                        let uu____24167 = equiv1 v1 v'  in
                                        if uu____24167
                                        then
                                          let uu____24170 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____24170 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____24186 -> []))
               in
            let uu____24191 =
              let wl =
                let uu___170_24195 = empty_worklist env  in
                {
                  attempting = (uu___170_24195.attempting);
                  wl_deferred = (uu___170_24195.wl_deferred);
                  ctr = (uu___170_24195.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_24195.smt_ok);
                  tcenv = (uu___170_24195.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24213  ->
                      match uu____24213 with
                      | (lb,v1) ->
                          let uu____24220 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____24220 with
                           | USolved wl1 -> ()
                           | uu____24222 -> fail1 lb v1)))
               in
            let rec check_ineq uu____24231 =
              match uu____24231 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24240) -> true
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
                      uu____24263,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24265,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24276) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24283,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24291 -> false)
               in
            let uu____24296 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24311  ->
                      match uu____24311 with
                      | (u,v1) ->
                          let uu____24318 = check_ineq (u, v1)  in
                          if uu____24318
                          then true
                          else
                            (let uu____24320 =
                               let uu____24321 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "GenUniverses")
                                  in
                               if uu____24321
                               then
                                 let uu____24322 =
                                   FStar_Syntax_Print.univ_to_string u  in
                                 let uu____24323 =
                                   FStar_Syntax_Print.univ_to_string v1  in
                                 FStar_Util.print2 "%s </= %s" uu____24322
                                   uu____24323
                               else ()  in
                             false)))
               in
            if uu____24296
            then ()
            else
              (let uu____24326 =
                 let uu____24327 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "GenUniverses")
                    in
                 if uu____24327
                 then
                   let uu____24328 =
                     let uu____24329 = ineqs_to_string (variables, ineqs)  in
                     FStar_Util.print1
                       "Partially solved inequality constraints are: %s\n"
                       uu____24329
                      in
                   let uu____24338 = FStar_Syntax_Unionfind.rollback tx  in
                   let uu____24339 = ineqs_to_string (variables, ineqs)  in
                   FStar_Util.print1
                     "Original solved inequality constraints are: %s\n"
                     uu____24339
                 else ()  in
               let uu____24349 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                   "Failed to solve universe inequalities for inductives")
                 uu____24349)
  
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
      let uu____24385 = solve_universe_inequalities' tx env ineqs  in
      FStar_Syntax_Unionfind.commit tx
  
let rec (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let fail1 uu____24406 =
        match uu____24406 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      let uu____24419 =
        let uu____24420 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "RelCheck")
           in
        if uu____24420
        then
          let uu____24421 = wl_to_string wl  in
          let uu____24422 =
            FStar_Util.string_of_int
              (FStar_List.length g.FStar_TypeChecker_Env.implicits)
             in
          FStar_Util.print2
            "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
            uu____24421 uu____24422
        else ()  in
      let g1 =
        let uu____24437 = solve_and_commit env wl fail1  in
        match uu____24437 with
        | FStar_Pervasives_Native.Some [] ->
            let uu___171_24450 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___171_24450.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred = [];
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___171_24450.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___171_24450.FStar_TypeChecker_Env.implicits)
            }
        | uu____24455 ->
            failwith "impossible: Unexpected deferred constraints remain"
         in
      let uu____24458 =
        solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs
         in
      let uu___172_24459 = g1  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___172_24459.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___172_24459.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], []);
        FStar_TypeChecker_Env.implicits =
          (uu___172_24459.FStar_TypeChecker_Env.implicits)
      }
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____24487 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24487 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          (let uu____24546 =
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ()
              in
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
            let uu___173_24610 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___173_24610.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___173_24610.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___173_24610.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24611 =
            let uu____24612 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24612  in
          if uu____24611
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 let uu____24619 =
                   if debug1
                   then
                     let uu____24620 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24621 =
                       let uu____24622 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24622
                        in
                     FStar_Errors.diag uu____24620 uu____24621
                   else ()  in
                 let vc1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops] env vc
                    in
                 let uu____24625 =
                   if debug1
                   then
                     let uu____24626 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24627 =
                       let uu____24628 =
                         FStar_Syntax_Print.term_to_string vc1  in
                       FStar_Util.format1 "After normalization VC=\n%s\n"
                         uu____24628
                        in
                     FStar_Errors.diag uu____24626 uu____24627
                   else ()  in
                 let uu____24630 =
                   let uu____24631 = FStar_TypeChecker_Env.get_range env  in
                   def_check_closed_in_env uu____24631 "discharge_guard'" env
                     vc1
                    in
                 let uu____24632 = check_trivial vc1  in
                 (match uu____24632 with
                  | FStar_TypeChecker_Common.Trivial  ->
                      FStar_Pervasives_Native.Some ret_g
                  | FStar_TypeChecker_Common.NonTrivial vc2 ->
                      if Prims.op_Negation use_smt
                      then
                        let uu____24638 =
                          if debug1
                          then
                            let uu____24639 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____24640 =
                              let uu____24641 =
                                FStar_Syntax_Print.term_to_string vc2  in
                              FStar_Util.format1
                                "Cannot solve without SMT : %s\n" uu____24641
                               in
                            FStar_Errors.diag uu____24639 uu____24640
                          else ()  in
                        FStar_Pervasives_Native.None
                      else
                        (let uu____24644 =
                           let uu____24645 =
                             if debug1
                             then
                               let uu____24646 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____24647 =
                                 let uu____24648 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____24648
                                  in
                               FStar_Errors.diag uu____24646 uu____24647
                             else ()  in
                           let vcs =
                             let uu____24659 = FStar_Options.use_tactics ()
                                in
                             if uu____24659
                             then
                               FStar_Options.with_saved_options
                                 (fun uu____24678  ->
                                    let uu____24679 =
                                      let uu____24680 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun a246  -> (Obj.magic ()) a246)
                                        uu____24680
                                       in
                                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                      env vc2)
                             else
                               (let uu____24682 =
                                  let uu____24689 = FStar_Options.peek ()  in
                                  (env, vc2, uu____24689)  in
                                [uu____24682])
                              in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____24723  ->
                                   match uu____24723 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal
                                          in
                                       let uu____24734 = check_trivial goal1
                                          in
                                       (match uu____24734 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____24735 =
                                              if debug1
                                              then
                                                FStar_Util.print_string
                                                  "Goal completely solved by tactic\n"
                                              else ()  in
                                            ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            let uu____24738 =
                                              FStar_Options.push ()  in
                                            let uu____24739 =
                                              FStar_Options.set opts  in
                                            let uu____24740 =
                                              maybe_update_proof_ns env1  in
                                            let uu____24741 =
                                              if debug1
                                              then
                                                let uu____24742 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1
                                                   in
                                                let uu____24743 =
                                                  let uu____24744 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2
                                                     in
                                                  let uu____24745 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1
                                                     in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____24744 uu____24745
                                                   in
                                                FStar_Errors.diag uu____24742
                                                  uu____24743
                                              else ()  in
                                            let uu____24747 =
                                              if debug1
                                              then
                                                let uu____24748 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1
                                                   in
                                                let uu____24749 =
                                                  let uu____24750 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2
                                                     in
                                                  FStar_Util.format1
                                                    "Before calling solver VC=\n%s\n"
                                                    uu____24750
                                                   in
                                                FStar_Errors.diag uu____24748
                                                  uu____24749
                                              else ()  in
                                            let res =
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2
                                               in
                                            let uu____24753 =
                                              FStar_Options.pop ()  in
                                            res)))
                            in
                         FStar_Pervasives_Native.Some ret_g)))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____24764 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24764 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____24771 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____24771
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____24782 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____24782 with
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
          let uu____24809 = FStar_Syntax_Unionfind.find u  in
          match uu____24809 with
          | FStar_Pervasives_Native.None  -> true
          | uu____24812 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____24832 = acc  in
          match uu____24832 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____24918 = hd1  in
                   (match uu____24918 with
                    | (uu____24931,env,u,tm,k,r) ->
                        let uu____24937 = unresolved u  in
                        if uu____24937
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___174_24967 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___174_24967.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___174_24967.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___174_24967.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___174_24967.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___174_24967.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___174_24967.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___174_24967.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___174_24967.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___174_24967.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___174_24967.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___174_24967.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___174_24967.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___174_24967.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___174_24967.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___174_24967.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___174_24967.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___174_24967.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___174_24967.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___174_24967.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___174_24967.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___174_24967.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___174_24967.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___174_24967.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___174_24967.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___174_24967.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___174_24967.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___174_24967.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___174_24967.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___174_24967.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___174_24967.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___174_24967.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___174_24967.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___174_24967.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___174_24967.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___174_24967.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___174_24967.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           let uu____24969 =
                             let uu____24970 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env1)
                                 (FStar_Options.Other "RelCheck")
                                in
                             if uu____24970
                             then
                               let uu____24971 =
                                 FStar_Syntax_Print.uvar_to_string u  in
                               let uu____24972 =
                                 FStar_Syntax_Print.term_to_string tm1  in
                               let uu____24973 =
                                 FStar_Syntax_Print.term_to_string k  in
                               FStar_Util.print3
                                 "Checking uvar %s resolved to %s at type %s\n"
                                 uu____24971 uu____24972 uu____24973
                             else ()  in
                           let g1 =
                             try
                               env1.FStar_TypeChecker_Env.check_type_of
                                 must_total env1 tm1 k
                             with
                             | e ->
                                 let uu____24983 =
                                   let uu____24984 =
                                     let uu____24993 =
                                       let uu____25000 =
                                         let uu____25001 =
                                           FStar_Syntax_Print.uvar_to_string
                                             u
                                            in
                                         let uu____25002 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env1 tm1
                                            in
                                         FStar_Util.format2
                                           "Failed while checking implicit %s set to %s"
                                           uu____25001 uu____25002
                                          in
                                       (FStar_Errors.Error_BadImplicit,
                                         uu____25000, r)
                                        in
                                     [uu____24993]  in
                                   FStar_Errors.add_errors uu____24984  in
                                 FStar_Exn.raise e
                              in
                           let g2 =
                             if env1.FStar_TypeChecker_Env.is_pattern
                             then
                               let uu___177_25016 = g1  in
                               {
                                 FStar_TypeChecker_Env.guard_f =
                                   FStar_TypeChecker_Common.Trivial;
                                 FStar_TypeChecker_Env.deferred =
                                   (uu___177_25016.FStar_TypeChecker_Env.deferred);
                                 FStar_TypeChecker_Env.univ_ineqs =
                                   (uu___177_25016.FStar_TypeChecker_Env.univ_ineqs);
                                 FStar_TypeChecker_Env.implicits =
                                   (uu___177_25016.FStar_TypeChecker_Env.implicits)
                               }
                             else g1  in
                           let g' =
                             let uu____25019 =
                               discharge_guard'
                                 (FStar_Pervasives_Native.Some
                                    (fun uu____25026  ->
                                       FStar_Syntax_Print.term_to_string tm1))
                                 env1 g2 true
                                in
                             match uu____25019 with
                             | FStar_Pervasives_Native.Some g3 -> g3
                             | FStar_Pervasives_Native.None  ->
                                 failwith
                                   "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                              in
                           until_fixpoint
                             ((FStar_List.append
                                 g'.FStar_TypeChecker_Env.implicits out),
                               true) tl1)))
           in
        let uu___178_25054 = g  in
        let uu____25055 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___178_25054.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___178_25054.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___178_25054.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____25055
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
        let uu____25117 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____25117 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25130 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a247  -> (Obj.magic ()) a247) uu____25130
      | (reason,uu____25132,uu____25133,e,t,r)::uu____25137 ->
          let uu____25164 =
            let uu____25169 =
              let uu____25170 = FStar_Syntax_Print.term_to_string t  in
              let uu____25171 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____25170 uu____25171
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____25169)
             in
          FStar_Errors.raise_error uu____25164 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___179_25182 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_25182.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_25182.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_25182.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____25209 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____25209 with
      | FStar_Pervasives_Native.Some uu____25215 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25231 = try_teq false env t1 t2  in
        match uu____25231 with
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
        let uu____25256 =
          let uu____25257 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Rel")
             in
          if uu____25257
          then
            let uu____25258 =
              FStar_TypeChecker_Normalize.term_to_string env t1  in
            let uu____25259 =
              FStar_TypeChecker_Normalize.term_to_string env t2  in
            FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25258
              uu____25259
          else ()  in
        let uu____25261 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
           in
        match uu____25261 with
        | (prob,x) ->
            let g =
              let uu____25277 =
                let uu____25280 = singleton' env prob true  in
                solve_and_commit env uu____25280
                  (fun uu____25282  -> FStar_Pervasives_Native.None)
                 in
              FStar_All.pipe_left (with_guard env prob) uu____25277  in
            let uu____25291 =
              let uu____25292 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel"))
                  && (FStar_Util.is_some g)
                 in
              if uu____25292
              then
                let uu____25293 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____25294 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                let uu____25295 =
                  let uu____25296 = FStar_Util.must g  in
                  guard_to_string env uu____25296  in
                FStar_Util.print3
                  "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                  uu____25293 uu____25294 uu____25295
              else ()  in
            (match g with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some g1 ->
                 FStar_Pervasives_Native.Some (x, g1))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25330 = check_subtyping env t1 t2  in
        match uu____25330 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25349 =
              let uu____25350 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____25350 g  in
            FStar_Pervasives_Native.Some uu____25349
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25368 = check_subtyping env t1 t2  in
        match uu____25368 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25387 =
              let uu____25388 =
                let uu____25389 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25389]  in
              close_guard env uu____25388 g  in
            FStar_Pervasives_Native.Some uu____25387
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25405 =
          let uu____25406 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Rel")
             in
          if uu____25406
          then
            let uu____25407 =
              FStar_TypeChecker_Normalize.term_to_string env t1  in
            let uu____25408 =
              FStar_TypeChecker_Normalize.term_to_string env t2  in
            FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25407
              uu____25408
          else ()  in
        let uu____25410 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
           in
        match uu____25410 with
        | (prob,x) ->
            let g =
              let uu____25420 =
                let uu____25423 = singleton' env prob false  in
                solve_and_commit env uu____25423
                  (fun uu____25425  -> FStar_Pervasives_Native.None)
                 in
              FStar_All.pipe_left (with_guard env prob) uu____25420  in
            (match g with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some g1 ->
                 let g2 =
                   let uu____25436 =
                     let uu____25437 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____25437]  in
                   close_guard env uu____25436 g1  in
                 discharge_guard_nosmt env g2)
  