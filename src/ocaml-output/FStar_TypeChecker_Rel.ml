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
        FStar_TypeChecker_Env.univ_ineqs = uu____30;
        FStar_TypeChecker_Env.implicits = uu____31;_} -> true
    | uu____58 -> false
  
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
          let uu___118_91 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___118_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_91.FStar_TypeChecker_Env.implicits)
          }
  
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____114 = FStar_Options.defensive ()  in
          if uu____114
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____118 =
              let uu____119 =
                let uu____120 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____120  in
              Prims.op_Negation uu____119  in
            (if uu____118
             then
               let uu____125 =
                 let uu____130 =
                   let uu____131 = FStar_Syntax_Print.term_to_string t  in
                   let uu____132 =
                     let uu____133 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____133
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____131 uu____132
                    in
                 (FStar_Errors.Warning_Defensive, uu____130)  in
               FStar_Errors.log_issue rng uu____125
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____149 =
          let uu____150 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____150  in
        if uu____149
        then ()
        else def_check_vars_in_set rng msg FStar_Syntax_Free.empty t
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____168 =
            let uu____169 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____169  in
          if uu____168
          then ()
          else
            (let uu____171 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____171 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____186 =
            let uu____187 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____187  in
          if uu____186
          then ()
          else
            (let uu____189 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____189 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___119_199 = g  in
          let uu____200 =
            let uu____201 =
              let uu____202 =
                let uu____205 =
                  let uu____206 =
                    let uu____221 =
                      let uu____224 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____224]  in
                    (f, uu____221)  in
                  FStar_Syntax_Syntax.Tm_app uu____206  in
                FStar_Syntax_Syntax.mk uu____205  in
              uu____202 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____201
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____200;
            FStar_TypeChecker_Env.deferred =
              (uu___119_199.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___119_199.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___119_199.FStar_TypeChecker_Env.implicits)
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
          let uu___120_242 = g  in
          let uu____243 =
            let uu____244 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____244  in
          {
            FStar_TypeChecker_Env.guard_f = uu____243;
            FStar_TypeChecker_Env.deferred =
              (uu___120_242.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___120_242.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___120_242.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____248 -> failwith "impossible"
  
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
          let uu____259 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____259
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____263 =
      let uu____264 = FStar_Syntax_Util.unmeta t  in
      uu____264.FStar_Syntax_Syntax.n  in
    match uu____263 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____268 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____299 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____299;
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
                       let uu____366 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____366
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___121_368 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___121_368.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___121_368.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___121_368.FStar_TypeChecker_Env.implicits)
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
               let uu____387 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____387
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
            let uu___122_400 = g  in
            let uu____401 =
              let uu____402 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____402  in
            {
              FStar_TypeChecker_Env.guard_f = uu____401;
              FStar_TypeChecker_Env.deferred =
                (uu___122_400.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___122_400.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___122_400.FStar_TypeChecker_Env.implicits)
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
        | uu____432 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____457 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____457  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____465 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____465, uv1)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____512 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____552 -> false
  
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
    match projectee with | Success _0 -> true | uu____738 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____754 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____777 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____781 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____785 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___88_808  ->
    match uu___88_808 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____814 =
        let uu____815 = FStar_Syntax_Subst.compress t  in
        uu____815.FStar_Syntax_Syntax.n  in
      match uu____814 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____844 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____845 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____844 uu____845
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____848;
             FStar_Syntax_Syntax.vars = uu____849;_},args)
          ->
          let uu____895 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____896 = FStar_Syntax_Print.term_to_string ty  in
          let uu____897 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____895 uu____896 uu____897
      | uu____898 -> "--"  in
    let uu____899 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____899 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___89_905  ->
      match uu___89_905 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____911 =
            let uu____914 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____915 =
              let uu____918 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____919 =
                let uu____922 =
                  let uu____925 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____925]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____922
                 in
              uu____918 :: uu____919  in
            uu____914 :: uu____915  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____911
      | FStar_TypeChecker_Common.CProb p ->
          let uu____931 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____932 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____933 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____931 uu____932
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____933
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___90_939  ->
      match uu___90_939 with
      | UNIV (u,t) ->
          let x =
            let uu____943 = FStar_Options.hide_uvar_nums ()  in
            if uu____943
            then "?"
            else
              (let uu____945 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____945 FStar_Util.string_of_int)
             in
          let uu____946 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____946
      | TERM ((u,uu____948),t) ->
          let x =
            let uu____955 = FStar_Options.hide_uvar_nums ()  in
            if uu____955
            then "?"
            else
              (let uu____957 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____957 FStar_Util.string_of_int)
             in
          let uu____958 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____958
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____969 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____969 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____981 =
      let uu____984 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____984
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____981 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____995 .
    (FStar_Syntax_Syntax.term,'Auu____995) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1012 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1030  ->
              match uu____1030 with
              | (x,uu____1036) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1012 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1042 =
      let uu____1043 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1043  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1042;
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
        let uu___123_1059 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___123_1059.wl_deferred);
          ctr = (uu___123_1059.ctr);
          defer_ok = (uu___123_1059.defer_ok);
          smt_ok;
          tcenv = (uu___123_1059.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1069 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1069,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___124_1090 = empty_worklist env  in
      let uu____1091 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1091;
        wl_deferred = (uu___124_1090.wl_deferred);
        ctr = (uu___124_1090.ctr);
        defer_ok = false;
        smt_ok = (uu___124_1090.smt_ok);
        tcenv = (uu___124_1090.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___125_1105 = wl  in
        {
          attempting = (uu___125_1105.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___125_1105.ctr);
          defer_ok = (uu___125_1105.defer_ok);
          smt_ok = (uu___125_1105.smt_ok);
          tcenv = (uu___125_1105.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___126_1122 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___126_1122.wl_deferred);
        ctr = (uu___126_1122.ctr);
        defer_ok = (uu___126_1122.defer_ok);
        smt_ok = (uu___126_1122.smt_ok);
        tcenv = (uu___126_1122.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1133 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1133
         then
           let uu____1134 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1134
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___91_1138  ->
    match uu___91_1138 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1142 'Auu____1143 .
    ('Auu____1142,'Auu____1143) FStar_TypeChecker_Common.problem ->
      ('Auu____1142,'Auu____1143) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___127_1160 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___127_1160.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___127_1160.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___127_1160.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___127_1160.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___127_1160.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___127_1160.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___127_1160.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1168 'Auu____1169 .
    ('Auu____1168,'Auu____1169) FStar_TypeChecker_Common.problem ->
      ('Auu____1168,'Auu____1169) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___92_1189  ->
    match uu___92_1189 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___93_1213  ->
      match uu___93_1213 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___94_1216  ->
    match uu___94_1216 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___95_1229  ->
    match uu___95_1229 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___96_1244  ->
    match uu___96_1244 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___97_1259  ->
    match uu___97_1259 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___98_1276  ->
    match uu___98_1276 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let def_scope_wf :
  'Auu____1295 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1295) FStar_Pervasives_Native.tuple2
          Prims.list -> Prims.unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1320 =
          let uu____1321 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1321  in
        if uu____1320
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1351)::bs ->
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
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1388 =
          let uu____1389 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1389  in
        if uu____1388
        then ()
        else
          (let uu____1391 =
             let uu____1394 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1394
              in
           def_check_closed_in (p_loc prob) msg uu____1391 phi)
  
let (def_check_prob :
  Prims.string -> FStar_TypeChecker_Common.prob -> Prims.unit) =
  fun msg  ->
    fun prob  ->
      (let uu____1420 =
         let uu____1421 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1421  in
       if uu____1420
       then ()
       else
         (let uu____1423 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1423));
      (let uu____1431 =
         FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard") prob uu____1431);
      (let uu____1437 =
         FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1437);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1448 -> ())
  
let (mk_eq2 :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun prob  ->
    fun t1  ->
      fun t2  ->
        let uu____1463 = FStar_Syntax_Util.type_u ()  in
        match uu____1463 with
        | (t_type,u) ->
            let uu____1470 =
              let uu____1475 = p_scope prob  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____1475 t_type  in
            (match uu____1470 with
             | (tt,uu____1477) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___99_1480  ->
    match uu___99_1480 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1502 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1502 = (Prims.parse_int "1")
  
let (next_pid : Prims.unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1514  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1599 'Auu____1600 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1599 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1599 ->
              'Auu____1600 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1599,'Auu____1600)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1637 = next_pid ()  in
                let uu____1638 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1637;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1638;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1652 'Auu____1653 .
    FStar_TypeChecker_Env.env ->
      'Auu____1652 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1652 ->
            'Auu____1653 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1652,'Auu____1653)
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
                let uu____1691 = next_pid ()  in
                let uu____1692 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1691;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1692;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____1705 'Auu____1706 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1705 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1705 ->
            'Auu____1706 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1705,'Auu____1706) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1739 = next_pid ()  in
              let uu____1740 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____1739;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____1740;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____1746 .
    worklist ->
      ('Auu____1746,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1796 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1796
        then
          let uu____1797 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1798 = prob_to_string env d  in
          let uu____1799 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1797 uu____1798 uu____1799 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1805 -> failwith "impossible"  in
           let uu____1806 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1820 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1821 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1820, uu____1821)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1827 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1828 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1827, uu____1828)
              in
           match uu____1806 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> Prims.unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___100_1844  ->
            match uu___100_1844 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1856 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1858),t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar u t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_1879  ->
           match uu___101_1879 with
           | UNIV uu____1882 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1888),t) ->
               let uu____1894 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1894
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
        (fun uu___102_1914  ->
           match uu___102_1914 with
           | UNIV (u',t) ->
               let uu____1919 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1919
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1923 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1930 =
        let uu____1931 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1931
         in
      FStar_Syntax_Subst.compress uu____1930
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1938 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1938
  
let norm_arg :
  'Auu____1942 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1942) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1942)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1963 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____1963, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____1994  ->
              match uu____1994 with
              | (x,imp) ->
                  let uu____2005 =
                    let uu___128_2006 = x  in
                    let uu____2007 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___128_2006.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___128_2006.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2007
                    }  in
                  (uu____2005, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2022 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2022
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2026 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2026
        | uu____2029 -> u2  in
      let uu____2030 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2030
  
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
                (let uu____2142 = norm_refinement env t12  in
                 match uu____2142 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2159;
                     FStar_Syntax_Syntax.vars = uu____2160;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2186 =
                       let uu____2187 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2188 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2187 uu____2188
                        in
                     failwith uu____2186)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2204 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2204
          | FStar_Syntax_Syntax.Tm_uinst uu____2205 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2242 =
                   let uu____2243 = FStar_Syntax_Subst.compress t1'  in
                   uu____2243.FStar_Syntax_Syntax.n  in
                 match uu____2242 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2260 -> aux true t1'
                 | uu____2267 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2282 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2313 =
                   let uu____2314 = FStar_Syntax_Subst.compress t1'  in
                   uu____2314.FStar_Syntax_Syntax.n  in
                 match uu____2313 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2331 -> aux true t1'
                 | uu____2338 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2353 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2398 =
                   let uu____2399 = FStar_Syntax_Subst.compress t1'  in
                   uu____2399.FStar_Syntax_Syntax.n  in
                 match uu____2398 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2416 -> aux true t1'
                 | uu____2423 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2438 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2453 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2468 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2483 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2498 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2525 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2556 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2577 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2608 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2635 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2672 ->
              let uu____2679 =
                let uu____2680 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2681 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2680 uu____2681
                 in
              failwith uu____2679
          | FStar_Syntax_Syntax.Tm_ascribed uu____2696 ->
              let uu____2723 =
                let uu____2724 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2725 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2724 uu____2725
                 in
              failwith uu____2723
          | FStar_Syntax_Syntax.Tm_delayed uu____2740 ->
              let uu____2765 =
                let uu____2766 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2767 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2766 uu____2767
                 in
              failwith uu____2765
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2782 =
                let uu____2783 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2784 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2783 uu____2784
                 in
              failwith uu____2782
           in
        let uu____2799 = whnf env t1  in aux false uu____2799
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____2821 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2821 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2844 = base_and_refinement env t  in
      FStar_All.pipe_right uu____2844 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2878 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2878, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____2884 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2884 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2905 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____2905 with
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
  fun uu____2984  ->
    match uu____2984 with
    | (t_base,refopt) ->
        let uu____3011 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3011 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3043 =
      let uu____3046 =
        let uu____3049 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3072  ->
                  match uu____3072 with | (uu____3079,uu____3080,x) -> x))
           in
        FStar_List.append wl.attempting uu____3049  in
      FStar_List.map (wl_prob_to_string wl) uu____3046  in
    FStar_All.pipe_right uu____3043 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3093 =
          let uu____3106 =
            let uu____3107 = FStar_Syntax_Subst.compress k  in
            uu____3107.FStar_Syntax_Syntax.n  in
          match uu____3106 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3160 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3160)
              else
                (let uu____3174 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3174 with
                 | (ys',t1,uu____3197) ->
                     let uu____3202 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3202))
          | uu____3243 ->
              let uu____3244 =
                let uu____3255 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3255)  in
              ((ys, t), uu____3244)
           in
        match uu____3093 with
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
                 let uu____3304 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3304 c  in
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
             let uu____3333 = p_guard prob  in
             match uu____3333 with
             | (uu____3338,uv) ->
                 ((let uu____3341 =
                     let uu____3342 = FStar_Syntax_Subst.compress uv  in
                     uu____3342.FStar_Syntax_Syntax.n  in
                   match uu____3341 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                       let bs = p_scope prob  in
                       let phi1 = u_abs k bs phi  in
                       ((let uu____3374 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3374
                         then
                           let uu____3375 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____3376 =
                             FStar_Syntax_Print.term_to_string uv  in
                           let uu____3377 =
                             FStar_Syntax_Print.term_to_string phi1  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3375
                             uu____3376 uu____3377
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3380 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___129_3383 = wl  in
                   {
                     attempting = (uu___129_3383.attempting);
                     wl_deferred = (uu___129_3383.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___129_3383.defer_ok);
                     smt_ok = (uu___129_3383.smt_ok);
                     tcenv = (uu___129_3383.tcenv)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3398 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3398
         then
           let uu____3399 = FStar_Util.string_of_int pid  in
           let uu____3400 =
             let uu____3401 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3401 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3399 uu____3400
         else ());
        commit sol;
        (let uu___130_3408 = wl  in
         {
           attempting = (uu___130_3408.attempting);
           wl_deferred = (uu___130_3408.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___130_3408.defer_ok);
           smt_ok = (uu___130_3408.smt_ok);
           tcenv = (uu___130_3408.tcenv)
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
             | (uu____3448,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3460 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____3460
              in
           (let uu____3466 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3466
            then
              let uu____3467 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3468 =
                let uu____3469 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3469 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3467 uu____3468
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
        let uu____3501 =
          let uu____3508 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3508 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3501
          (FStar_Util.for_some
             (fun uu____3544  ->
                match uu____3544 with
                | (uv,uu____3550) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3557 'Auu____3558 .
    'Auu____3557 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3558)
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
            let uu____3590 = occurs wl uk t  in Prims.op_Negation uu____3590
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3597 =
                 let uu____3598 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____3599 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3598 uu____3599
                  in
               FStar_Pervasives_Native.Some uu____3597)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____3609 'Auu____3610 .
    'Auu____3609 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3610)
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
            let uu____3664 = occurs_check env wl uk t  in
            match uu____3664 with
            | (occurs_ok,msg) ->
                let uu____3695 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3695, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____3718 'Auu____3719 .
    (FStar_Syntax_Syntax.bv,'Auu____3718) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3719) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3719) FStar_Pervasives_Native.tuple2
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
      let uu____3803 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3857  ->
                fun uu____3858  ->
                  match (uu____3857, uu____3858) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3939 =
                        let uu____3940 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____3940  in
                      if uu____3939
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____3965 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____3965
                         then
                           let uu____3978 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____3978)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____3803 with | (isect,uu____4019) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4044 'Auu____4045 .
    (FStar_Syntax_Syntax.bv,'Auu____4044) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4045) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4100  ->
              fun uu____4101  ->
                match (uu____4100, uu____4101) with
                | ((a,uu____4119),(b,uu____4121)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4135 'Auu____4136 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4135) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4136)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4136)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4187 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4201  ->
                      match uu____4201 with
                      | (b,uu____4207) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4187
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4223 -> FStar_Pervasives_Native.None
  
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
            let uu____4296 = pat_var_opt env seen hd1  in
            (match uu____4296 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4310 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4310
                   then
                     let uu____4311 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4311
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4329 =
      let uu____4330 = FStar_Syntax_Subst.compress t  in
      uu____4330.FStar_Syntax_Syntax.n  in
    match uu____4329 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4333 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4350;
           FStar_Syntax_Syntax.pos = uu____4351;
           FStar_Syntax_Syntax.vars = uu____4352;_},uu____4353)
        -> true
    | uu____4390 -> false
  
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
           FStar_Syntax_Syntax.pos = uu____4514;
           FStar_Syntax_Syntax.vars = uu____4515;_},args)
        -> (t, uv, k, args)
    | uu____4583 -> failwith "Not a flex-uvar"
  
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
      let uu____4660 = destruct_flex_t t  in
      match uu____4660 with
      | (t1,uv,k,args) ->
          let uu____4775 = pat_vars env [] args  in
          (match uu____4775 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4873 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4954 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4989 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4993 -> false
  
let string_of_option :
  'Auu____4997 .
    ('Auu____4997 -> Prims.string) ->
      'Auu____4997 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___103_5010  ->
      match uu___103_5010 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5016 = f x  in Prims.strcat "Some " uu____5016
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___104_5019  ->
    match uu___104_5019 with
    | MisMatch (d1,d2) ->
        let uu____5030 =
          let uu____5031 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5032 =
            let uu____5033 =
              let uu____5034 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5034 ")"  in
            Prims.strcat ") (" uu____5033  in
          Prims.strcat uu____5031 uu____5032  in
        Prims.strcat "MisMatch (" uu____5030
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___105_5037  ->
    match uu___105_5037 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5052 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5078 = m2 ()  in
          (match uu____5078 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5093 -> HeadMatch)
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
          let uu____5103 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5103 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5114 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5133 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5142 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5170 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5170
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5171 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5172 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5173 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5190 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5203 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5227) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5233,uu____5234) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5276) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5297;
             FStar_Syntax_Syntax.index = uu____5298;
             FStar_Syntax_Syntax.sort = t2;_},uu____5300)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5307 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5308 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5309 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5322 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5329 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5347 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5347
  
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
            let uu____5368 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5368
            then FullMatch
            else
              (let uu____5370 =
                 let uu____5379 =
                   let uu____5382 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5382  in
                 let uu____5383 =
                   let uu____5386 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5386  in
                 (uu____5379, uu____5383)  in
               MisMatch uu____5370)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5392),FStar_Syntax_Syntax.Tm_uinst (g,uu____5394)) ->
            let uu____5403 = head_matches env f g  in
            FStar_All.pipe_right uu____5403 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5406 = FStar_Const.eq_const c d  in
            if uu____5406
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5413),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5415)) ->
            let uu____5464 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5464
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5471),FStar_Syntax_Syntax.Tm_refine (y,uu____5473)) ->
            let uu____5482 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5482 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5484),uu____5485) ->
            let uu____5490 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5490 head_match
        | (uu____5491,FStar_Syntax_Syntax.Tm_refine (x,uu____5493)) ->
            let uu____5498 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5498 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5499,FStar_Syntax_Syntax.Tm_type
           uu____5500) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5501,FStar_Syntax_Syntax.Tm_arrow uu____5502) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5528),FStar_Syntax_Syntax.Tm_app (head',uu____5530))
            ->
            let uu____5571 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5571 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5573),uu____5574) ->
            let uu____5595 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5595 head_match
        | (uu____5596,FStar_Syntax_Syntax.Tm_app (head1,uu____5598)) ->
            let uu____5619 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5619 head_match
        | uu____5620 ->
            let uu____5625 =
              let uu____5634 = delta_depth_of_term env t11  in
              let uu____5637 = delta_depth_of_term env t21  in
              (uu____5634, uu____5637)  in
            MisMatch uu____5625
  
let head_matches_delta :
  'Auu____5649 .
    FStar_TypeChecker_Env.env ->
      'Auu____5649 ->
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
            let uu____5682 = FStar_Syntax_Util.head_and_args t  in
            match uu____5682 with
            | (head1,uu____5700) ->
                let uu____5721 =
                  let uu____5722 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5722.FStar_Syntax_Syntax.n  in
                (match uu____5721 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5728 =
                       let uu____5729 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5729 FStar_Option.isSome
                        in
                     if uu____5728
                     then
                       let uu____5748 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____5748
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5752 -> FStar_Pervasives_Native.None)
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
              let uu____5863 =
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
              match uu____5863 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____5904 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____5904 with
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
                 uu____5936),uu____5937)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____5955 =
                     let uu____5964 = maybe_inline t11  in
                     let uu____5967 = maybe_inline t21  in
                     (uu____5964, uu____5967)  in
                   match uu____5955 with
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
                (uu____6004,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6005))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6023 =
                     let uu____6032 = maybe_inline t11  in
                     let uu____6035 = maybe_inline t21  in
                     (uu____6032, uu____6035)  in
                   match uu____6023 with
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
            | MisMatch uu____6084 -> fail1 r
            | uu____6093 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6106 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6106
           then
             let uu____6107 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6108 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6109 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6116 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6134 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6134
                    (fun uu____6168  ->
                       match uu____6168 with
                       | (t11,t21) ->
                           let uu____6175 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6176 =
                             let uu____6177 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6177  in
                           Prims.strcat uu____6175 uu____6176))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____6107
               uu____6108 uu____6109 uu____6116
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6211 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6247 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___106_6259  ->
    match uu___106_6259 with
    | T (t,uu____6261) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6277 = FStar_Syntax_Util.type_u ()  in
      match uu____6277 with
      | (t,uu____6283) ->
          let uu____6284 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6284
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6295 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6295 FStar_Pervasives_Native.fst
  
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
        let uu____6359 = head_matches env t1 t'  in
        match uu____6359 with
        | MisMatch uu____6360 -> false
        | uu____6369 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6465,imp),T (t2,uu____6468)) -> (t2, imp)
                     | uu____6487 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6554  ->
                    match uu____6554 with
                    | (t2,uu____6568) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6611 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6611 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6686))::tcs2) ->
                       aux
                         (((let uu___131_6721 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_6721.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_6721.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6739 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___107_6792 =
                 match uu___107_6792 with
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
               let uu____6909 = decompose1 [] bs1  in
               (rebuild, matches, uu____6909))
      | uu____6958 ->
          let rebuild uu___108_6964 =
            match uu___108_6964 with
            | [] -> t1
            | uu____6967 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___109_6998  ->
    match uu___109_6998 with
    | T (t,uu____7000) -> t
    | uu____7009 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___110_7012  ->
    match uu___110_7012 with
    | T (t,uu____7014) -> FStar_Syntax_Syntax.as_arg t
    | uu____7023 -> failwith "Impossible"
  
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
              | (uu____7139,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7164 = new_uvar r scope1 k  in
                  (match uu____7164 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7182 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7199 =
                         let uu____7200 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7200
                          in
                       ((T (gi_xs, mk_kind)), uu____7199))
              | (uu____7213,uu____7214,C uu____7215) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7362 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7379;
                         FStar_Syntax_Syntax.vars = uu____7380;_})
                        ->
                        let uu____7403 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7403 with
                         | (T (gi_xs,uu____7427),prob) ->
                             let uu____7437 =
                               let uu____7438 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7438
                                in
                             (uu____7437, [prob])
                         | uu____7441 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7456;
                         FStar_Syntax_Syntax.vars = uu____7457;_})
                        ->
                        let uu____7480 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7480 with
                         | (T (gi_xs,uu____7504),prob) ->
                             let uu____7514 =
                               let uu____7515 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7515
                                in
                             (uu____7514, [prob])
                         | uu____7518 -> failwith "impossible")
                    | (uu____7529,uu____7530,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7532;
                         FStar_Syntax_Syntax.vars = uu____7533;_})
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
                        let uu____7664 =
                          let uu____7673 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7673 FStar_List.unzip
                           in
                        (match uu____7664 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7727 =
                                 let uu____7728 =
                                   let uu____7731 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7731 un_T  in
                                 let uu____7732 =
                                   let uu____7741 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7741
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7728;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7732;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7727
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7750 ->
                        let uu____7763 = sub_prob scope1 args q  in
                        (match uu____7763 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7362 with
                   | (tc,probs) ->
                       let uu____7794 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7857,uu____7858),T
                            (t,uu____7860)) ->
                             let b1 =
                               ((let uu___132_7897 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___132_7897.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___132_7897.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7898 =
                               let uu____7905 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7905 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7898)
                         | uu____7940 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7794 with
                        | (bopt,scope2,args1) ->
                            let uu____8024 = aux scope2 args1 qs2  in
                            (match uu____8024 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8062 =
                                           let uu____8065 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8065  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8062
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
                                         let uu____8090 =
                                           let uu____8093 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8094 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8093 :: uu____8094  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8090
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
  'Auu____8163 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8163)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8163)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___133_8184 = p  in
      let uu____8189 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8190 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___133_8184.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8189;
        FStar_TypeChecker_Common.relation =
          (uu___133_8184.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8190;
        FStar_TypeChecker_Common.element =
          (uu___133_8184.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___133_8184.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___133_8184.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___133_8184.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___133_8184.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___133_8184.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8202 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8202
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8211 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8231 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8231 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8241 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8241 with
           | (lh,uu____8261) ->
               let uu____8282 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8282 with
                | (rh,uu____8302) ->
                    let uu____8323 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8340,FStar_Syntax_Syntax.Tm_uvar uu____8341)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8378,uu____8379)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8400,FStar_Syntax_Syntax.Tm_uvar uu____8401)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8422,uu____8423)
                          ->
                          let uu____8440 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8440 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8489 ->
                                    let rank =
                                      let uu____8497 = is_top_level_prob prob
                                         in
                                      if uu____8497
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8499 =
                                      let uu___134_8504 = tp  in
                                      let uu____8509 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___134_8504.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___134_8504.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___134_8504.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8509;
                                        FStar_TypeChecker_Common.element =
                                          (uu___134_8504.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___134_8504.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___134_8504.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___134_8504.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___134_8504.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___134_8504.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8499)))
                      | (uu____8520,FStar_Syntax_Syntax.Tm_uvar uu____8521)
                          ->
                          let uu____8538 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8538 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8587 ->
                                    let uu____8594 =
                                      let uu___135_8601 = tp  in
                                      let uu____8606 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_8601.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8606;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_8601.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___135_8601.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_8601.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_8601.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_8601.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_8601.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_8601.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_8601.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8594)))
                      | (uu____8623,uu____8624) -> (rigid_rigid, tp)  in
                    (match uu____8323 with
                     | (rank,tp1) ->
                         let uu____8643 =
                           FStar_All.pipe_right
                             (let uu___136_8649 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___136_8649.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___136_8649.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___136_8649.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___136_8649.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___136_8649.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___136_8649.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___136_8649.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___136_8649.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___136_8649.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8643))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8659 =
            FStar_All.pipe_right
              (let uu___137_8665 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_8665.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_8665.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_8665.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_8665.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_8665.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_8665.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___137_8665.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_8665.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_8665.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8659)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8720 probs =
      match uu____8720 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8773 = rank wl hd1  in
               (match uu____8773 with
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
    match projectee with | UDeferred _0 -> true | uu____8880 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8892 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8904 -> false
  
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
                        let uu____8944 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8944 with
                        | (k,uu____8950) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8960 -> false)))
            | uu____8961 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9009 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9015 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9015 = (Prims.parse_int "0")))
                           in
                        if uu____9009 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9029 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9035 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9035 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9029)
               in
            let uu____9036 = filter1 u12  in
            let uu____9039 = filter1 u22  in (uu____9036, uu____9039)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9062 = filter_out_common_univs us1 us2  in
                (match uu____9062 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9115 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9115 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9118 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9128 =
                          let uu____9129 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9130 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9129
                            uu____9130
                           in
                        UFailed uu____9128))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9150 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9150 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9172 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9172 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9175 ->
                let uu____9180 =
                  let uu____9181 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9182 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9181
                    uu____9182 msg
                   in
                UFailed uu____9180
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9183,uu____9184) ->
              let uu____9185 =
                let uu____9186 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9187 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9186 uu____9187
                 in
              failwith uu____9185
          | (FStar_Syntax_Syntax.U_unknown ,uu____9188) ->
              let uu____9189 =
                let uu____9190 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9191 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9190 uu____9191
                 in
              failwith uu____9189
          | (uu____9192,FStar_Syntax_Syntax.U_bvar uu____9193) ->
              let uu____9194 =
                let uu____9195 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9196 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9195 uu____9196
                 in
              failwith uu____9194
          | (uu____9197,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9198 =
                let uu____9199 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9200 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9199 uu____9200
                 in
              failwith uu____9198
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9224 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9224
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9246 = occurs_univ v1 u3  in
              if uu____9246
              then
                let uu____9247 =
                  let uu____9248 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9249 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9248 uu____9249
                   in
                try_umax_components u11 u21 uu____9247
              else
                (let uu____9251 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9251)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9271 = occurs_univ v1 u3  in
              if uu____9271
              then
                let uu____9272 =
                  let uu____9273 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9274 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9273 uu____9274
                   in
                try_umax_components u11 u21 uu____9272
              else
                (let uu____9276 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9276)
          | (FStar_Syntax_Syntax.U_max uu____9285,uu____9286) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9292 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9292
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9294,FStar_Syntax_Syntax.U_max uu____9295) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9301 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9301
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9303,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9304,FStar_Syntax_Syntax.U_name
             uu____9305) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9306) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9307) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9308,FStar_Syntax_Syntax.U_succ
             uu____9309) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9310,FStar_Syntax_Syntax.U_zero
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
      let uu____9396 = bc1  in
      match uu____9396 with
      | (bs1,mk_cod1) ->
          let uu____9437 = bc2  in
          (match uu____9437 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9541 = aux xs ys  in
                     (match uu____9541 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9624 =
                       let uu____9631 = mk_cod1 xs  in ([], uu____9631)  in
                     let uu____9634 =
                       let uu____9641 = mk_cod2 ys  in ([], uu____9641)  in
                     (uu____9624, uu____9634)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9752 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9752
       then
         let uu____9753 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9753
       else ());
      (let uu____9755 = next_prob probs  in
       match uu____9755 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___138_9776 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___138_9776.wl_deferred);
               ctr = (uu___138_9776.ctr);
               defer_ok = (uu___138_9776.defer_ok);
               smt_ok = (uu___138_9776.smt_ok);
               tcenv = (uu___138_9776.tcenv)
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
                  let uu____9787 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9787 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9792 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9792 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9797,uu____9798) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9815 ->
                let uu____9824 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9883  ->
                          match uu____9883 with
                          | (c,uu____9891,uu____9892) -> c < probs.ctr))
                   in
                (match uu____9824 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9933 =
                            FStar_List.map
                              (fun uu____9948  ->
                                 match uu____9948 with
                                 | (uu____9959,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9933
                      | uu____9962 ->
                          let uu____9971 =
                            let uu___139_9972 = probs  in
                            let uu____9973 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9994  ->
                                      match uu____9994 with
                                      | (uu____10001,uu____10002,y) -> y))
                               in
                            {
                              attempting = uu____9973;
                              wl_deferred = rest;
                              ctr = (uu___139_9972.ctr);
                              defer_ok = (uu___139_9972.defer_ok);
                              smt_ok = (uu___139_9972.smt_ok);
                              tcenv = (uu___139_9972.tcenv)
                            }  in
                          solve env uu____9971))))

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
            let uu____10009 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10009 with
            | USolved wl1 ->
                let uu____10011 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10011
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
                  let uu____10057 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10057 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10060 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10072;
                  FStar_Syntax_Syntax.vars = uu____10073;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10076;
                  FStar_Syntax_Syntax.vars = uu____10077;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10091,uu____10092) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10099,FStar_Syntax_Syntax.Tm_uinst uu____10100) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10107 -> USolved wl

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
            ((let uu____10117 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10117
              then
                let uu____10118 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10118 msg
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
        (let uu____10127 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10127
         then
           let uu____10128 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10128
         else ());
        (let uu____10130 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10130 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10192 = head_matches_delta env () t1 t2  in
               match uu____10192 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10233 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10282 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10297 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10298 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10297, uu____10298)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10303 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10304 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10303, uu____10304)
                           in
                        (match uu____10282 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10330 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10330
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10361 =
                                    let uu____10370 =
                                      let uu____10373 =
                                        let uu____10376 =
                                          let uu____10377 =
                                            let uu____10384 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10384)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10377
                                           in
                                        FStar_Syntax_Syntax.mk uu____10376
                                         in
                                      uu____10373
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10392 =
                                      let uu____10395 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10395]  in
                                    (uu____10370, uu____10392)  in
                                  FStar_Pervasives_Native.Some uu____10361
                              | (uu____10408,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10410)) ->
                                  let uu____10415 =
                                    let uu____10422 =
                                      let uu____10425 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10425]  in
                                    (t11, uu____10422)  in
                                  FStar_Pervasives_Native.Some uu____10415
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10435),uu____10436) ->
                                  let uu____10441 =
                                    let uu____10448 =
                                      let uu____10451 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10451]  in
                                    (t21, uu____10448)  in
                                  FStar_Pervasives_Native.Some uu____10441
                              | uu____10460 ->
                                  let uu____10465 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10465 with
                                   | (head1,uu____10489) ->
                                       let uu____10510 =
                                         let uu____10511 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10511.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10510 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10522;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_constant_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10524;_}
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
                                        | uu____10531 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10544) ->
                  let uu____10569 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___111_10595  ->
                            match uu___111_10595 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10602 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10602 with
                                      | (u',uu____10618) ->
                                          let uu____10639 =
                                            let uu____10640 = whnf env u'  in
                                            uu____10640.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10639 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10644) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10669 -> false))
                                 | uu____10670 -> false)
                            | uu____10673 -> false))
                     in
                  (match uu____10569 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10707 tps =
                         match uu____10707 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10755 =
                                    let uu____10764 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10764  in
                                  (match uu____10755 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10799 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10808 =
                         let uu____10817 =
                           let uu____10824 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10824, [])  in
                         make_lower_bound uu____10817 lower_bounds  in
                       (match uu____10808 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10836 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10836
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
                            ((let uu____10856 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10856
                              then
                                let wl' =
                                  let uu___140_10858 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___140_10858.wl_deferred);
                                    ctr = (uu___140_10858.ctr);
                                    defer_ok = (uu___140_10858.defer_ok);
                                    smt_ok = (uu___140_10858.smt_ok);
                                    tcenv = (uu___140_10858.tcenv)
                                  }  in
                                let uu____10859 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10859
                              else ());
                             (let uu____10861 =
                                solve_t env eq_prob
                                  (let uu___141_10863 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___141_10863.wl_deferred);
                                     ctr = (uu___141_10863.ctr);
                                     defer_ok = (uu___141_10863.defer_ok);
                                     smt_ok = (uu___141_10863.smt_ok);
                                     tcenv = (uu___141_10863.tcenv)
                                   })
                                 in
                              match uu____10861 with
                              | Success uu____10866 ->
                                  let wl1 =
                                    let uu___142_10868 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___142_10868.wl_deferred);
                                      ctr = (uu___142_10868.ctr);
                                      defer_ok = (uu___142_10868.defer_ok);
                                      smt_ok = (uu___142_10868.smt_ok);
                                      tcenv = (uu___142_10868.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10870 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10875 -> FStar_Pervasives_Native.None))))
              | uu____10876 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10885 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10885
         then
           let uu____10886 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10886
         else ());
        (let uu____10888 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10888 with
         | (u,args) ->
             let uu____10927 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10927 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10968 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10968 with
                    | (h1,args1) ->
                        let uu____11009 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11009 with
                         | (h2,uu____11029) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11056 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11056
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11074 =
                                          let uu____11077 =
                                            let uu____11078 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____11078
                                             in
                                          [uu____11077]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11074))
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
                                       (let uu____11111 =
                                          let uu____11114 =
                                            let uu____11115 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____11115
                                             in
                                          [uu____11114]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11111))
                                  else FStar_Pervasives_Native.None
                              | uu____11129 -> FStar_Pervasives_Native.None))
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
                             let uu____11219 =
                               let uu____11228 =
                                 let uu____11231 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11231  in
                               (uu____11228, m1)  in
                             FStar_Pervasives_Native.Some uu____11219)
                    | (uu____11244,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11246)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11294),uu____11295) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11342 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11395) ->
                       let uu____11420 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___112_11446  ->
                                 match uu___112_11446 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11453 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11453 with
                                           | (u',uu____11469) ->
                                               let uu____11490 =
                                                 let uu____11491 =
                                                   whnf env u'  in
                                                 uu____11491.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11490 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11495) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11520 -> false))
                                      | uu____11521 -> false)
                                 | uu____11524 -> false))
                          in
                       (match uu____11420 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11562 tps =
                              match uu____11562 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11624 =
                                         let uu____11635 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11635  in
                                       (match uu____11624 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11686 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11697 =
                              let uu____11708 =
                                let uu____11717 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11717, [])  in
                              make_upper_bound uu____11708 upper_bounds  in
                            (match uu____11697 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11731 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11731
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
                                 ((let uu____11757 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11757
                                   then
                                     let wl' =
                                       let uu___143_11759 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___143_11759.wl_deferred);
                                         ctr = (uu___143_11759.ctr);
                                         defer_ok = (uu___143_11759.defer_ok);
                                         smt_ok = (uu___143_11759.smt_ok);
                                         tcenv = (uu___143_11759.tcenv)
                                       }  in
                                     let uu____11760 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11760
                                   else ());
                                  (let uu____11762 =
                                     solve_t env eq_prob
                                       (let uu___144_11764 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___144_11764.wl_deferred);
                                          ctr = (uu___144_11764.ctr);
                                          defer_ok =
                                            (uu___144_11764.defer_ok);
                                          smt_ok = (uu___144_11764.smt_ok);
                                          tcenv = (uu___144_11764.tcenv)
                                        })
                                      in
                                   match uu____11762 with
                                   | Success uu____11767 ->
                                       let wl1 =
                                         let uu___145_11769 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___145_11769.wl_deferred);
                                           ctr = (uu___145_11769.ctr);
                                           defer_ok =
                                             (uu___145_11769.defer_ok);
                                           smt_ok = (uu___145_11769.smt_ok);
                                           tcenv = (uu___145_11769.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11771 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11776 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11777 -> failwith "Impossible: Not a flex-rigid")))

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
              (let uu____11795 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____11795
               then
                 let uu____11796 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____11797 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____11796 (rel_to_string (p_rel orig)) uu____11797
               else ());
              (let rec aux scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let rhs_prob = rhs scope env1 subst1  in
                     ((let uu____11857 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____11857
                       then
                         let uu____11858 = prob_to_string env1 rhs_prob  in
                         FStar_Util.print1 "rhs_prob = %s\n" uu____11858
                       else ());
                      (let formula =
                         FStar_All.pipe_right (p_guard rhs_prob)
                           FStar_Pervasives_Native.fst
                          in
                       FStar_Util.Inl ([rhs_prob], formula)))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___146_11912 = hd1  in
                       let uu____11913 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___146_11912.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___146_11912.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11913
                       }  in
                     let hd21 =
                       let uu___147_11917 = hd2  in
                       let uu____11918 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___147_11917.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___147_11917.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11918
                       }  in
                     let prob =
                       let uu____11922 =
                         let uu____11927 =
                           FStar_All.pipe_left invert_rel (p_rel orig)  in
                         mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                           uu____11927 hd21.FStar_Syntax_Syntax.sort
                           FStar_Pervasives_Native.None "Formal parameter"
                          in
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                         uu____11922
                        in
                     let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                     let subst2 =
                       let uu____11938 =
                         FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                           subst1
                          in
                       (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                         :: uu____11938
                        in
                     let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                     let uu____11942 =
                       aux (FStar_List.append scope [(hd12, imp)]) env2
                         subst2 xs1 ys1
                        in
                     (match uu____11942 with
                      | FStar_Util.Inl (sub_probs,phi) ->
                          let phi1 =
                            let uu____11980 =
                              FStar_All.pipe_right (p_guard prob)
                                FStar_Pervasives_Native.fst
                               in
                            let uu____11985 =
                              close_forall env2 [(hd12, imp)] phi  in
                            FStar_Syntax_Util.mk_conj uu____11980 uu____11985
                             in
                          ((let uu____11995 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env2)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11995
                            then
                              let uu____11996 =
                                FStar_Syntax_Print.term_to_string phi1  in
                              let uu____11997 =
                                FStar_Syntax_Print.bv_to_string hd12  in
                              FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                uu____11996 uu____11997
                            else ());
                           FStar_Util.Inl ((prob :: sub_probs), phi1))
                      | fail1 -> fail1)
                 | uu____12020 ->
                     FStar_Util.Inr "arity or argument-qualifier mismatch"
                  in
               let scope = p_scope orig  in
               let uu____12030 = aux scope env [] bs1 bs2  in
               match uu____12030 with
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
        (let uu____12055 = compress_tprob wl problem  in
         solve_t' env uu____12055 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12089 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12089 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12120,uu____12121) ->
                    let rec may_relate head3 =
                      let uu____12146 =
                        let uu____12147 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12147.FStar_Syntax_Syntax.n  in
                      match uu____12146 with
                      | FStar_Syntax_Syntax.Tm_name uu____12150 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12151 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12174;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____12175;
                            FStar_Syntax_Syntax.fv_qual = uu____12176;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12179;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12180;
                            FStar_Syntax_Syntax.fv_qual = uu____12181;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12185,uu____12186) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12228) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12234) ->
                          may_relate t
                      | uu____12239 -> false  in
                    let uu____12240 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12240
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
                                 let uu____12257 =
                                   let uu____12258 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12258 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12257
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____12260 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____12260
                    else
                      (let uu____12262 =
                         let uu____12263 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12264 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12263 uu____12264
                          in
                       giveup env1 uu____12262 orig)
                | (uu____12265,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___148_12279 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_12279.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_12279.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___148_12279.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_12279.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_12279.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_12279.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_12279.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_12279.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12280,FStar_Pervasives_Native.None ) ->
                    ((let uu____12292 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12292
                      then
                        let uu____12293 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12294 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12295 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12296 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____12293 uu____12294 uu____12295 uu____12296
                      else ());
                     (let uu____12298 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12298 with
                      | (head11,args1) ->
                          let uu____12335 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12335 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12389 =
                                   let uu____12390 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12391 = args_to_string args1  in
                                   let uu____12392 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12393 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12390 uu____12391 uu____12392
                                     uu____12393
                                    in
                                 giveup env1 uu____12389 orig
                               else
                                 (let uu____12395 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12401 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12401 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12395
                                  then
                                    let uu____12402 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12402 with
                                    | USolved wl2 ->
                                        let uu____12404 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12404
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12408 =
                                       base_and_refinement env1 t1  in
                                     match uu____12408 with
                                     | (base1,refinement1) ->
                                         let uu____12433 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12433 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____12490 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____12490 with
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
                                                            (fun uu____12512 
                                                               ->
                                                               fun
                                                                 uu____12513 
                                                                 ->
                                                                 match 
                                                                   (uu____12512,
                                                                    uu____12513)
                                                                 with
                                                                 | ((a,uu____12531),
                                                                    (a',uu____12533))
                                                                    ->
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12547
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12542)
                                                            args1 args2
                                                           in
                                                        ((let uu____12553 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env1)
                                                              (FStar_Options.Other
                                                                 "Rel")
                                                             in
                                                          if uu____12553
                                                          then
                                                            let uu____12554 =
                                                              FStar_Syntax_Print.list_to_string
                                                                (prob_to_string
                                                                   env1)
                                                                subprobs
                                                               in
                                                            FStar_Util.print1
                                                              "Adding subproblems for arguments: %s"
                                                              uu____12554
                                                          else ());
                                                         (let formula =
                                                            let uu____12557 =
                                                              FStar_List.map
                                                                (fun p  ->
                                                                   FStar_Pervasives_Native.fst
                                                                    (p_guard
                                                                    p))
                                                                subprobs
                                                               in
                                                            FStar_Syntax_Util.mk_conj_l
                                                              uu____12557
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
                                               | uu____12563 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___149_12599 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___149_12599.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____12632 =
           match uu____12632 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____12674 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____12674 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____12770  ->
                      let uu____12771 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____12771);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____12839  ->
                                match uu____12839 with
                                | (x,imp) ->
                                    let uu____12850 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____12850, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____12863 = FStar_Syntax_Util.type_u ()  in
                        match uu____12863 with
                        | (t1,uu____12869) ->
                            let uu____12870 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____12870
                         in
                      let uu____12875 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____12875 with
                       | (t',tm_u1) ->
                           let uu____12888 = destruct_flex_t t'  in
                           (match uu____12888 with
                            | (uu____12925,u1,k1,uu____12928) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____12987 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____12987
                                   in
                                let sol =
                                  let uu____12991 =
                                    let uu____13000 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13000)  in
                                  TERM uu____12991  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____13135  ->
                            let uu____13136 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____13137 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13136 uu____13137);
                       (let uu____13150 = pat_var_opt env pat_args hd1  in
                        match uu____13150 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____13170  ->
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
                                       (fun uu____13213  ->
                                          match uu____13213 with
                                          | (x,uu____13219) ->
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
                                 (fun uu____13234  ->
                                    let uu____13235 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____13248 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____13235
                                      uu____13248);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____13252 =
                                  let uu____13253 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____13253  in
                                if uu____13252
                                then
                                  (debug1
                                     (fun uu____13265  ->
                                        let uu____13266 =
                                          let uu____13269 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____13282 =
                                            let uu____13285 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____13286 =
                                              let uu____13289 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____13290 =
                                                let uu____13293 =
                                                  names_to_string fvs  in
                                                let uu____13294 =
                                                  let uu____13297 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____13297]  in
                                                uu____13293 :: uu____13294
                                                 in
                                              uu____13289 :: uu____13290  in
                                            uu____13285 :: uu____13286  in
                                          uu____13269 :: uu____13282  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____13266);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____13299 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____13302 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____13299 (formal ::
                                     pattern_vars) uu____13302 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____13309::uu____13310) ->
                      let uu____13341 =
                        let uu____13354 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____13354  in
                      (match uu____13341 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____13393 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____13400::uu____13401,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____13424 =
                 let uu____13437 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____13437  in
               (match uu____13424 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____13473  ->
                          let uu____13474 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____13475 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____13476 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____13477 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____13474 uu____13475 uu____13476 uu____13477);
                     (let uu____13478 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____13481 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____13478 [] uu____13481 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____13515 = lhs  in
           match uu____13515 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____13525 ->
                     let uu____13526 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____13526 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____13549 = p  in
           match uu____13549 with
           | (((u,k),xs,c),ps,(h,uu____13560,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13642 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____13642 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____13665 = h gs_xs  in
                      let uu____13666 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         in
                      FStar_Syntax_Util.abs xs1 uu____13665 uu____13666  in
                    ((let uu____13672 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13672
                      then
                        let uu____13673 =
                          let uu____13676 =
                            let uu____13677 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____13677
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____13682 =
                            let uu____13685 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____13686 =
                              let uu____13689 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____13690 =
                                let uu____13693 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____13694 =
                                  let uu____13697 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____13698 =
                                    let uu____13701 =
                                      let uu____13702 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____13702
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____13707 =
                                      let uu____13710 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____13710]  in
                                    uu____13701 :: uu____13707  in
                                  uu____13697 :: uu____13698  in
                                uu____13693 :: uu____13694  in
                              uu____13689 :: uu____13690  in
                            uu____13685 :: uu____13686  in
                          uu____13676 :: uu____13682  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____13673
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___113_13732 =
           match uu___113_13732 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____13764 = p  in
           match uu____13764 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13855 = FStar_List.nth ps i  in
               (match uu____13855 with
                | (pi,uu____13859) ->
                    let uu____13864 = FStar_List.nth xs i  in
                    (match uu____13864 with
                     | (xi,uu____13876) ->
                         let rec gs k =
                           let uu____13889 =
                             let uu____13902 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____13902  in
                           match uu____13889 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____13977)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____13990 = new_uvar r xs k_a  in
                                     (match uu____13990 with
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
                                          let uu____14012 = aux subst2 tl1
                                             in
                                          (match uu____14012 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____14039 =
                                                 let uu____14042 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____14042 :: gi_xs'  in
                                               let uu____14043 =
                                                 let uu____14046 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____14046 :: gi_ps'  in
                                               (uu____14039, uu____14043)))
                                  in
                               aux [] bs
                            in
                         let uu____14051 =
                           let uu____14052 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____14052
                            in
                         if uu____14051
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____14056 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____14056 with
                            | (g_xs,uu____14068) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____14079 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____14080 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_58  ->
                                         FStar_Pervasives_Native.Some _0_58)
                                     in
                                  FStar_Syntax_Util.abs xs uu____14079
                                    uu____14080
                                   in
                                let sub1 =
                                  let uu____14086 =
                                    let uu____14091 = p_scope orig  in
                                    let uu____14092 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____14095 =
                                      let uu____14098 =
                                        FStar_List.map
                                          (fun uu____14113  ->
                                             match uu____14113 with
                                             | (uu____14122,uu____14123,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____14098  in
                                    mk_problem uu____14091 orig uu____14092
                                      (p_rel orig) uu____14095
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_59  ->
                                       FStar_TypeChecker_Common.TProb _0_59)
                                    uu____14086
                                   in
                                ((let uu____14138 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14138
                                  then
                                    let uu____14139 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____14140 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____14139 uu____14140
                                  else ());
                                 (let wl2 =
                                    let uu____14143 =
                                      let uu____14146 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____14146
                                       in
                                    solve_prob orig uu____14143
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____14155 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_60  ->
                                       FStar_Pervasives_Native.Some _0_60)
                                    uu____14155)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____14186 = lhs  in
           match uu____14186 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____14222 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____14222 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____14255 =
                         let uu____14302 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____14302)  in
                       FStar_Pervasives_Native.Some uu____14255
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____14446 =
                            let uu____14453 =
                              let uu____14454 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____14454.FStar_Syntax_Syntax.n  in
                            (uu____14453, args)  in
                          match uu____14446 with
                          | (uu____14465,[]) ->
                              let uu____14468 =
                                let uu____14479 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____14479)  in
                              FStar_Pervasives_Native.Some uu____14468
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____14500,uu____14501) ->
                              let uu____14522 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14522 with
                               | (uv1,uv_args) ->
                                   let uu____14565 =
                                     let uu____14566 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14566.FStar_Syntax_Syntax.n  in
                                   (match uu____14565 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14576) ->
                                        let uu____14601 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14601 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14628  ->
                                                       let uu____14629 =
                                                         let uu____14630 =
                                                           let uu____14631 =
                                                             let uu____14636
                                                               =
                                                               let uu____14637
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14637
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14636
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14631
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14630
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14629))
                                                in
                                             let c1 =
                                               let uu____14647 =
                                                 let uu____14648 =
                                                   let uu____14653 =
                                                     let uu____14654 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14654
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14653
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14648
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14647
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14667 =
                                                 let uu____14670 =
                                                   let uu____14671 =
                                                     let uu____14674 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14674
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14671
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14670
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14667
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14693 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____14698,uu____14699) ->
                              let uu____14718 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14718 with
                               | (uv1,uv_args) ->
                                   let uu____14761 =
                                     let uu____14762 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14762.FStar_Syntax_Syntax.n  in
                                   (match uu____14761 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14772) ->
                                        let uu____14797 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14797 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14824  ->
                                                       let uu____14825 =
                                                         let uu____14826 =
                                                           let uu____14827 =
                                                             let uu____14832
                                                               =
                                                               let uu____14833
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14833
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14832
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14827
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14826
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14825))
                                                in
                                             let c1 =
                                               let uu____14843 =
                                                 let uu____14844 =
                                                   let uu____14849 =
                                                     let uu____14850 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14850
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14849
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14844
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14843
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14863 =
                                                 let uu____14866 =
                                                   let uu____14867 =
                                                     let uu____14870 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14870
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14867
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14866
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14863
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14889 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____14896) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____14937 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____14937
                                  (fun _0_61  ->
                                     FStar_Pervasives_Native.Some _0_61)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____14973 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____14973 with
                                   | (args1,rest) ->
                                       let uu____15002 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____15002 with
                                        | (xs2,c2) ->
                                            let uu____15015 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____15015
                                              (fun uu____15039  ->
                                                 match uu____15039 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____15079 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____15079 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15147 =
                                         let uu____15152 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____15152
                                          in
                                       FStar_All.pipe_right uu____15147
                                         (fun _0_62  ->
                                            FStar_Pervasives_Native.Some
                                              _0_62))
                          | uu____15167 ->
                              let uu____15174 =
                                let uu____15179 =
                                  let uu____15180 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____15181 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____15182 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____15180 uu____15181 uu____15182
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____15179)
                                 in
                              FStar_Errors.raise_error uu____15174
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____15189 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____15189
                          (fun uu____15244  ->
                             match uu____15244 with
                             | (xs1,c1) ->
                                 let uu____15293 =
                                   let uu____15334 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____15334)
                                    in
                                 FStar_Pervasives_Native.Some uu____15293))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____15455 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____15469 = project orig env wl1 i st  in
                      match uu____15469 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15483) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____15498 = imitate orig env wl1 st  in
                   match uu____15498 with
                   | Failed uu____15503 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____15534 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____15534 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____15557 = forced_lhs_pattern  in
                     (match uu____15557 with
                      | (lhs_t,uu____15559,uu____15560,uu____15561) ->
                          ((let uu____15563 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15563
                            then
                              let uu____15564 = lhs1  in
                              match uu____15564 with
                              | (t0,uu____15566,uu____15567,uu____15568) ->
                                  let uu____15569 = forced_lhs_pattern  in
                                  (match uu____15569 with
                                   | (t11,uu____15571,uu____15572,uu____15573)
                                       ->
                                       let uu____15574 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____15575 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____15574 uu____15575)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____15583 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____15583
                            then
                              ((let uu____15585 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15585
                                then
                                  let uu____15586 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____15587 = names_to_string rhs_vars
                                     in
                                  let uu____15588 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____15586 uu____15587 uu____15588
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____15592 =
                                  let uu____15593 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____15593 wl2  in
                                match uu____15592 with
                                | Failed uu____15594 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____15603 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15603
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____15616 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____15616 with
                 | (hd1,uu____15632) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____15653 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____15666 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____15667 -> true
                      | uu____15684 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____15688 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____15688
                          then true
                          else
                            ((let uu____15691 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____15691
                              then
                                let uu____15692 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____15692
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
                    let uu____15712 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____15712 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____15725 =
                             let uu____15726 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____15726
                              in
                           giveup_or_defer1 orig uu____15725
                         else
                           (let uu____15728 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____15728
                            then
                              let uu____15729 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____15729
                               then
                                 let uu____15730 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____15730
                               else
                                 ((let uu____15735 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____15735
                                   then
                                     let uu____15736 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____15737 = names_to_string fvs1
                                        in
                                     let uu____15738 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____15736 uu____15737 uu____15738
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
                                (let uu____15742 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____15742
                                 then
                                   ((let uu____15744 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____15744
                                     then
                                       let uu____15745 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____15746 = names_to_string fvs1
                                          in
                                       let uu____15747 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____15745 uu____15746 uu____15747
                                     else ());
                                    (let uu____15749 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____15749))
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
                      (let uu____15760 =
                         let uu____15761 = FStar_Syntax_Free.names t1  in
                         check_head uu____15761 t2  in
                       if uu____15760
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____15772 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15772
                           then
                             let uu____15773 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____15774 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____15773 uu____15774
                           else ());
                          (let uu____15782 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____15782))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____15859 uu____15860 r =
                match (uu____15859, uu____15860) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____16058 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____16058
                    then
                      let uu____16059 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____16059
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____16083 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____16083
                        then
                          let uu____16084 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____16085 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____16086 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____16087 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____16088 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16084 uu____16085 uu____16086 uu____16087
                            uu____16088
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____16148 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____16148 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____16162 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____16162 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____16216 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____16216
                                      in
                                   let uu____16219 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____16219 k3)
                            else
                              (let uu____16223 =
                                 let uu____16224 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____16225 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____16226 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____16224 uu____16225 uu____16226
                                  in
                               failwith uu____16223)
                           in
                        let uu____16227 =
                          let uu____16234 =
                            let uu____16247 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____16247  in
                          match uu____16234 with
                          | (bs,k1') ->
                              let uu____16272 =
                                let uu____16285 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____16285
                                 in
                              (match uu____16272 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____16313 =
                                       let uu____16318 = p_scope orig  in
                                       mk_problem uu____16318 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_63  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_63) uu____16313
                                      in
                                   let uu____16323 =
                                     let uu____16328 =
                                       let uu____16329 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____16329.FStar_Syntax_Syntax.n  in
                                     let uu____16332 =
                                       let uu____16333 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____16333.FStar_Syntax_Syntax.n  in
                                     (uu____16328, uu____16332)  in
                                   (match uu____16323 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____16342,uu____16343) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____16346,FStar_Syntax_Syntax.Tm_type
                                       uu____16347) -> (k2'_ys, [sub_prob])
                                    | uu____16350 ->
                                        let uu____16355 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____16355 with
                                         | (t,uu____16367) ->
                                             let uu____16368 =
                                               new_uvar r zs t  in
                                             (match uu____16368 with
                                              | (k_zs,uu____16380) ->
                                                  let kprob =
                                                    let uu____16382 =
                                                      let uu____16387 =
                                                        p_scope orig  in
                                                      mk_problem uu____16387
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_64  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_64) uu____16382
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____16227 with
                        | (k_u',sub_probs) ->
                            let uu____16400 =
                              let uu____16411 =
                                let uu____16412 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____16412
                                 in
                              let uu____16421 =
                                let uu____16424 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____16424  in
                              let uu____16427 =
                                let uu____16430 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____16430  in
                              (uu____16411, uu____16421, uu____16427)  in
                            (match uu____16400 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____16449 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____16449 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____16468 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____16468
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
                                            let uu____16472 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____16472 with
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
              let solve_one_pat uu____16525 uu____16526 =
                match (uu____16525, uu____16526) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____16644 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____16644
                      then
                        let uu____16645 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____16646 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____16645 uu____16646
                      else ());
                     (let uu____16648 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____16648
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____16667  ->
                               fun uu____16668  ->
                                 match (uu____16667, uu____16668) with
                                 | ((a,uu____16686),(t21,uu____16688)) ->
                                     let uu____16697 =
                                       let uu____16702 = p_scope orig  in
                                       let uu____16703 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____16702 orig
                                         uu____16703
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____16697
                                       (fun _0_65  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_65)) xs args2
                           in
                        let guard =
                          let uu____16709 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____16709  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____16724 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____16724 with
                         | (occurs_ok,uu____16732) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____16740 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____16740
                             then
                               let sol =
                                 let uu____16742 =
                                   let uu____16751 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____16751)  in
                                 TERM uu____16742  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____16758 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____16758
                                then
                                  let uu____16759 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____16759 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____16783,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____16809 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____16809
                                        then
                                          let uu____16810 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____16810
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____16817 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____16819 = lhs  in
              match uu____16819 with
              | (t1,u1,k1,args1) ->
                  let uu____16824 = rhs  in
                  (match uu____16824 with
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
                        | uu____16864 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____16874 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____16874 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____16892) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____16899 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____16899
                                     then
                                       let uu____16900 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____16900
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____16907 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____16910 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____16910
          then
            let uu____16911 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____16911
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____16915 = FStar_Util.physical_equality t1 t2  in
             if uu____16915
             then
               let uu____16916 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____16916
             else
               ((let uu____16919 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____16919
                 then
                   let uu____16920 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____16921 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16922 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____16920
                     uu____16921 uu____16922
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____16925,uu____16926)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____16951,FStar_Syntax_Syntax.Tm_delayed uu____16952)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____16977,uu____16978)
                     ->
                     let uu____17005 =
                       let uu___150_17006 = problem  in
                       let uu____17007 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_17006.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17007;
                         FStar_TypeChecker_Common.relation =
                           (uu___150_17006.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___150_17006.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___150_17006.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_17006.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_17006.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_17006.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_17006.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_17006.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17005 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____17008,uu____17009) ->
                     let uu____17016 =
                       let uu___151_17017 = problem  in
                       let uu____17018 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_17017.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17018;
                         FStar_TypeChecker_Common.relation =
                           (uu___151_17017.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___151_17017.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___151_17017.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_17017.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_17017.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_17017.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_17017.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_17017.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17016 wl
                 | (uu____17019,FStar_Syntax_Syntax.Tm_ascribed uu____17020)
                     ->
                     let uu____17047 =
                       let uu___152_17048 = problem  in
                       let uu____17049 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_17048.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___152_17048.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___152_17048.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17049;
                         FStar_TypeChecker_Common.element =
                           (uu___152_17048.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_17048.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___152_17048.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_17048.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_17048.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_17048.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17047 wl
                 | (uu____17050,FStar_Syntax_Syntax.Tm_meta uu____17051) ->
                     let uu____17058 =
                       let uu___153_17059 = problem  in
                       let uu____17060 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___153_17059.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___153_17059.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___153_17059.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17060;
                         FStar_TypeChecker_Common.element =
                           (uu___153_17059.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___153_17059.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___153_17059.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___153_17059.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___153_17059.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___153_17059.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17058 wl
                 | (FStar_Syntax_Syntax.Tm_quoted
                    (t11,uu____17062),FStar_Syntax_Syntax.Tm_quoted
                    (t21,uu____17064)) ->
                     let uu____17073 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____17073
                 | (FStar_Syntax_Syntax.Tm_bvar uu____17074,uu____17075) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____17076,FStar_Syntax_Syntax.Tm_bvar uu____17077) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___114_17132 =
                       match uu___114_17132 with
                       | [] -> c
                       | bs ->
                           let uu____17154 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____17154
                        in
                     let uu____17163 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____17163 with
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
                                     let uu____17305 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____17305
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____17307 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_66  ->
                                        FStar_TypeChecker_Common.CProb _0_66)
                                     uu____17307))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___115_17383 =
                       match uu___115_17383 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____17417 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____17417 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____17553 =
                                     let uu____17558 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____17559 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____17558
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____17559
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_67  ->
                                        FStar_TypeChecker_Common.TProb _0_67)
                                     uu____17553))
                 | (FStar_Syntax_Syntax.Tm_abs uu____17564,uu____17565) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17590 -> true
                       | uu____17607 -> false  in
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
                         (let uu____17654 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_17662 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_17662.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_17662.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_17662.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_17662.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_17662.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_17662.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_17662.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_17662.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_17662.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_17662.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_17662.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_17662.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_17662.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_17662.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_17662.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_17662.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_17662.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_17662.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_17662.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_17662.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_17662.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_17662.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_17662.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_17662.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_17662.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_17662.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_17662.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_17662.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_17662.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_17662.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_17662.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_17662.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_17662.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_17662.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17654 with
                          | (uu____17665,ty,uu____17667) ->
                              let uu____17668 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17668)
                        in
                     let uu____17669 =
                       let uu____17686 = maybe_eta t1  in
                       let uu____17693 = maybe_eta t2  in
                       (uu____17686, uu____17693)  in
                     (match uu____17669 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_17735 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_17735.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_17735.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_17735.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_17735.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_17735.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_17735.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_17735.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_17735.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____17758 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17758
                          then
                            let uu____17759 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17759 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_17774 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_17774.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_17774.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_17774.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_17774.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_17774.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_17774.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_17774.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_17774.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____17798 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17798
                          then
                            let uu____17799 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17799 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_17814 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_17814.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_17814.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_17814.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_17814.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_17814.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_17814.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_17814.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_17814.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____17818 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____17835,FStar_Syntax_Syntax.Tm_abs uu____17836) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17861 -> true
                       | uu____17878 -> false  in
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
                         (let uu____17925 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___154_17933 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___154_17933.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___154_17933.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___154_17933.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___154_17933.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___154_17933.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___154_17933.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___154_17933.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___154_17933.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___154_17933.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___154_17933.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___154_17933.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___154_17933.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___154_17933.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___154_17933.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___154_17933.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___154_17933.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___154_17933.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___154_17933.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___154_17933.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___154_17933.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___154_17933.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___154_17933.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___154_17933.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___154_17933.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___154_17933.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___154_17933.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___154_17933.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___154_17933.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___154_17933.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___154_17933.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___154_17933.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___154_17933.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___154_17933.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___154_17933.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17925 with
                          | (uu____17936,ty,uu____17938) ->
                              let uu____17939 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17939)
                        in
                     let uu____17940 =
                       let uu____17957 = maybe_eta t1  in
                       let uu____17964 = maybe_eta t2  in
                       (uu____17957, uu____17964)  in
                     (match uu____17940 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___155_18006 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18006.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___155_18006.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18006.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18006.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18006.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18006.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18006.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18006.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18029 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18029
                          then
                            let uu____18030 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18030 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18045 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18045.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18045.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18045.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18045.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18045.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18045.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18045.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18045.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18069 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18069
                          then
                            let uu____18070 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18070 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___156_18085 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___156_18085.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___156_18085.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___156_18085.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___156_18085.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___156_18085.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___156_18085.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___156_18085.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___156_18085.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18089 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____18121 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____18121) &&
                          (let uu____18133 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____18133))
                         &&
                         (let uu____18148 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____18148 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___116_18158 =
                                match uu___116_18158 with
                                | FStar_Syntax_Syntax.Delta_constant_at_level
                                    uu____18159 -> true
                                | uu____18160 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____18161 -> false)
                        in
                     let uu____18162 = as_refinement should_delta env wl t1
                        in
                     (match uu____18162 with
                      | (x11,phi1) ->
                          let uu____18169 =
                            as_refinement should_delta env wl t2  in
                          (match uu____18169 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____18177 =
                                   let uu____18182 = p_scope orig  in
                                   mk_problem uu____18182 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____18177
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
                                 let uu____18216 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____18216
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____18220 =
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
                                   let uu____18226 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____18226 impl
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
                                   let uu____18235 =
                                     let uu____18240 =
                                       let uu____18241 = p_scope orig  in
                                       let uu____18248 =
                                         let uu____18255 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____18255]  in
                                       FStar_List.append uu____18241
                                         uu____18248
                                        in
                                     mk_problem uu____18240 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_69  ->
                                        FStar_TypeChecker_Common.TProb _0_69)
                                     uu____18235
                                    in
                                 let uu____18264 =
                                   solve env1
                                     (let uu___157_18266 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___157_18266.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___157_18266.smt_ok);
                                        tcenv = (uu___157_18266.tcenv)
                                      })
                                    in
                                 (match uu____18264 with
                                  | Failed uu____18273 -> fallback ()
                                  | Success uu____18278 ->
                                      let guard =
                                        let uu____18282 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____18287 =
                                          let uu____18288 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____18288
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____18282
                                          uu____18287
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___158_18297 = wl1  in
                                        {
                                          attempting =
                                            (uu___158_18297.attempting);
                                          wl_deferred =
                                            (uu___158_18297.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___158_18297.defer_ok);
                                          smt_ok = (uu___158_18297.smt_ok);
                                          tcenv = (uu___158_18297.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18299,FStar_Syntax_Syntax.Tm_uvar uu____18300) ->
                     let uu____18333 = destruct_flex_t t1  in
                     let uu____18334 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18333 uu____18334
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18335;
                       FStar_Syntax_Syntax.pos = uu____18336;
                       FStar_Syntax_Syntax.vars = uu____18337;_},uu____18338),FStar_Syntax_Syntax.Tm_uvar
                    uu____18339) ->
                     let uu____18392 = destruct_flex_t t1  in
                     let uu____18393 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18392 uu____18393
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18394,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18395;
                       FStar_Syntax_Syntax.pos = uu____18396;
                       FStar_Syntax_Syntax.vars = uu____18397;_},uu____18398))
                     ->
                     let uu____18451 = destruct_flex_t t1  in
                     let uu____18452 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18451 uu____18452
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18453;
                       FStar_Syntax_Syntax.pos = uu____18454;
                       FStar_Syntax_Syntax.vars = uu____18455;_},uu____18456),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18457;
                       FStar_Syntax_Syntax.pos = uu____18458;
                       FStar_Syntax_Syntax.vars = uu____18459;_},uu____18460))
                     ->
                     let uu____18533 = destruct_flex_t t1  in
                     let uu____18534 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18533 uu____18534
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18535,uu____18536) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18553 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18553 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18560;
                       FStar_Syntax_Syntax.pos = uu____18561;
                       FStar_Syntax_Syntax.vars = uu____18562;_},uu____18563),uu____18564)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18601 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18601 t2 wl
                 | (uu____18608,FStar_Syntax_Syntax.Tm_uvar uu____18609) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____18626,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18627;
                       FStar_Syntax_Syntax.pos = uu____18628;
                       FStar_Syntax_Syntax.vars = uu____18629;_},uu____18630))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18667,FStar_Syntax_Syntax.Tm_type uu____18668) ->
                     solve_t' env
                       (let uu___159_18686 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_18686.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_18686.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_18686.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_18686.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_18686.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_18686.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_18686.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_18686.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_18686.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18687;
                       FStar_Syntax_Syntax.pos = uu____18688;
                       FStar_Syntax_Syntax.vars = uu____18689;_},uu____18690),FStar_Syntax_Syntax.Tm_type
                    uu____18691) ->
                     solve_t' env
                       (let uu___159_18729 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_18729.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_18729.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_18729.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_18729.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_18729.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_18729.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_18729.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_18729.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_18729.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18730,FStar_Syntax_Syntax.Tm_arrow uu____18731) ->
                     solve_t' env
                       (let uu___159_18761 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_18761.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_18761.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_18761.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_18761.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_18761.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_18761.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_18761.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_18761.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_18761.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18762;
                       FStar_Syntax_Syntax.pos = uu____18763;
                       FStar_Syntax_Syntax.vars = uu____18764;_},uu____18765),FStar_Syntax_Syntax.Tm_arrow
                    uu____18766) ->
                     solve_t' env
                       (let uu___159_18816 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___159_18816.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___159_18816.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___159_18816.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___159_18816.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___159_18816.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___159_18816.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___159_18816.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___159_18816.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___159_18816.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18817,uu____18818) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____18837 =
                          let uu____18838 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____18838
                           in
                        if uu____18837
                        then
                          let uu____18839 =
                            FStar_All.pipe_left
                              (fun _0_70  ->
                                 FStar_TypeChecker_Common.TProb _0_70)
                              (let uu___160_18845 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_18845.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_18845.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_18845.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_18845.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_18845.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_18845.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_18845.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_18845.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_18845.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____18846 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____18839 uu____18846 t2
                            wl
                        else
                          (let uu____18854 = base_and_refinement env t2  in
                           match uu____18854 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18883 =
                                      FStar_All.pipe_left
                                        (fun _0_71  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_71)
                                        (let uu___161_18889 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_18889.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_18889.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_18889.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_18889.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_18889.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_18889.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_18889.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_18889.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_18889.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____18890 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____18883
                                      uu____18890 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_18904 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_18904.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_18904.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____18907 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_72  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_72) uu____18907
                                       in
                                    let guard =
                                      let uu____18919 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18919
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
                         uu____18927;
                       FStar_Syntax_Syntax.pos = uu____18928;
                       FStar_Syntax_Syntax.vars = uu____18929;_},uu____18930),uu____18931)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____18970 =
                          let uu____18971 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____18971
                           in
                        if uu____18970
                        then
                          let uu____18972 =
                            FStar_All.pipe_left
                              (fun _0_73  ->
                                 FStar_TypeChecker_Common.TProb _0_73)
                              (let uu___160_18978 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_18978.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___160_18978.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___160_18978.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_18978.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_18978.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___160_18978.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_18978.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_18978.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_18978.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____18979 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____18972 uu____18979 t2
                            wl
                        else
                          (let uu____18987 = base_and_refinement env t2  in
                           match uu____18987 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19016 =
                                      FStar_All.pipe_left
                                        (fun _0_74  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_74)
                                        (let uu___161_19022 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___161_19022.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___161_19022.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___161_19022.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___161_19022.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___161_19022.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___161_19022.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___161_19022.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___161_19022.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___161_19022.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19023 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19016
                                      uu____19023 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___162_19037 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___162_19037.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___162_19037.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19040 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_75  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_75) uu____19040
                                       in
                                    let guard =
                                      let uu____19052 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19052
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____19060,FStar_Syntax_Syntax.Tm_uvar uu____19061) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19079 = base_and_refinement env t1  in
                        match uu____19079 with
                        | (t_base,uu____19091) ->
                            solve_t env
                              (let uu___163_19105 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_19105.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_19105.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_19105.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_19105.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_19105.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_19105.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_19105.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_19105.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____19106,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19107;
                       FStar_Syntax_Syntax.pos = uu____19108;
                       FStar_Syntax_Syntax.vars = uu____19109;_},uu____19110))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19148 = base_and_refinement env t1  in
                        match uu____19148 with
                        | (t_base,uu____19160) ->
                            solve_t env
                              (let uu___163_19174 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___163_19174.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___163_19174.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___163_19174.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___163_19174.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___163_19174.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___163_19174.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___163_19174.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___163_19174.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____19175,uu____19176) ->
                     let t21 =
                       let uu____19186 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____19186  in
                     solve_t env
                       (let uu___164_19210 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___164_19210.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___164_19210.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___164_19210.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___164_19210.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___164_19210.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___164_19210.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___164_19210.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___164_19210.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___164_19210.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19211,FStar_Syntax_Syntax.Tm_refine uu____19212) ->
                     let t11 =
                       let uu____19222 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____19222  in
                     solve_t env
                       (let uu___165_19246 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_19246.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_19246.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_19246.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_19246.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_19246.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_19246.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_19246.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_19246.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_19246.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match
                    (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                     let sc_prob =
                       let uu____19326 =
                         let uu____19331 = p_scope orig  in
                         mk_problem uu____19331 orig t11
                           FStar_TypeChecker_Common.EQ t21
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       FStar_All.pipe_left
                         (fun _0_76  -> FStar_TypeChecker_Common.TProb _0_76)
                         uu____19326
                        in
                     let rec solve_branches brs11 brs21 =
                       match (brs11, brs21) with
                       | (br1::rs1,br2::rs2) ->
                           let uu____19517 = br1  in
                           (match uu____19517 with
                            | (p1,w1,uu____19536) ->
                                let uu____19549 = br2  in
                                (match uu____19549 with
                                 | (p2,w2,uu____19564) ->
                                     let uu____19569 =
                                       let uu____19570 =
                                         FStar_Syntax_Syntax.eq_pat p1 p2  in
                                       Prims.op_Negation uu____19570  in
                                     if uu____19569
                                     then FStar_Pervasives_Native.None
                                     else
                                       (let uu____19578 =
                                          FStar_Syntax_Subst.open_branch' br1
                                           in
                                        match uu____19578 with
                                        | ((p11,w11,e1),s) ->
                                            let uu____19621 = br2  in
                                            (match uu____19621 with
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
                                                   let uu____19652 =
                                                     p_scope orig  in
                                                   let uu____19659 =
                                                     let uu____19666 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____19666
                                                      in
                                                   FStar_List.append
                                                     uu____19652 uu____19659
                                                    in
                                                 let uu____19677 =
                                                   match (w11, w22) with
                                                   | (FStar_Pervasives_Native.Some
                                                      uu____19692,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      uu____19705) ->
                                                       FStar_Pervasives_Native.None
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) ->
                                                       FStar_Pervasives_Native.Some
                                                         []
                                                   | (FStar_Pervasives_Native.Some
                                                      w12,FStar_Pervasives_Native.Some
                                                      w23) ->
                                                       let uu____19738 =
                                                         let uu____19741 =
                                                           let uu____19742 =
                                                             mk_problem scope
                                                               orig w12
                                                               FStar_TypeChecker_Common.EQ
                                                               w23
                                                               FStar_Pervasives_Native.None
                                                               "when clause"
                                                              in
                                                           FStar_All.pipe_left
                                                             (fun _0_77  ->
                                                                FStar_TypeChecker_Common.TProb
                                                                  _0_77)
                                                             uu____19742
                                                            in
                                                         [uu____19741]  in
                                                       FStar_Pervasives_Native.Some
                                                         uu____19738
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____19677
                                                   (fun wprobs  ->
                                                      let prob =
                                                        let uu____19766 =
                                                          mk_problem scope
                                                            orig e1
                                                            FStar_TypeChecker_Common.EQ
                                                            e21
                                                            FStar_Pervasives_Native.None
                                                            "branch body"
                                                           in
                                                        FStar_All.pipe_left
                                                          (fun _0_78  ->
                                                             FStar_TypeChecker_Common.TProb
                                                               _0_78)
                                                          uu____19766
                                                         in
                                                      let uu____19777 =
                                                        solve_branches rs1
                                                          rs2
                                                         in
                                                      FStar_Util.bind_opt
                                                        uu____19777
                                                        (fun r1  ->
                                                           FStar_Pervasives_Native.Some
                                                             (prob ::
                                                             (FStar_List.append
                                                                wprobs r1))))))))
                       | ([],[]) -> FStar_Pervasives_Native.Some []
                       | uu____19838 -> FStar_Pervasives_Native.None  in
                     let uu____19869 = solve_branches brs1 brs2  in
                     (match uu____19869 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env "Tm_match branches don't match" orig
                      | FStar_Pervasives_Native.Some sub_probs ->
                          let sub_probs1 = sc_prob :: sub_probs  in
                          let wl1 =
                            solve_prob orig FStar_Pervasives_Native.None []
                              wl
                             in
                          solve env (attempt sub_probs1 wl1))
                 | (FStar_Syntax_Syntax.Tm_match uu____19885,uu____19886) ->
                     let head1 =
                       let uu____19912 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19912
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19956 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19956
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19998 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19998
                       then
                         let uu____19999 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20000 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20001 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19999 uu____20000 uu____20001
                       else ());
                      (let uu____20003 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20003
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20018 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20018
                          then
                            let guard =
                              let uu____20030 =
                                let uu____20031 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20031 = FStar_Syntax_Util.Equal  in
                              if uu____20030
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20035 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_79  ->
                                      FStar_Pervasives_Native.Some _0_79)
                                   uu____20035)
                               in
                            let uu____20038 = solve_prob orig guard [] wl  in
                            solve env uu____20038
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____20041,uu____20042) ->
                     let head1 =
                       let uu____20052 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20052
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20096 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20096
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20138 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20138
                       then
                         let uu____20139 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20140 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20141 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20139 uu____20140 uu____20141
                       else ());
                      (let uu____20143 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20143
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20158 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20158
                          then
                            let guard =
                              let uu____20170 =
                                let uu____20171 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20171 = FStar_Syntax_Util.Equal  in
                              if uu____20170
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20175 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_80  ->
                                      FStar_Pervasives_Native.Some _0_80)
                                   uu____20175)
                               in
                            let uu____20178 = solve_prob orig guard [] wl  in
                            solve env uu____20178
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____20181,uu____20182) ->
                     let head1 =
                       let uu____20186 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20186
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20230 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20230
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20272 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20272
                       then
                         let uu____20273 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20274 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20275 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20273 uu____20274 uu____20275
                       else ());
                      (let uu____20277 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20277
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20292 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20292
                          then
                            let guard =
                              let uu____20304 =
                                let uu____20305 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20305 = FStar_Syntax_Util.Equal  in
                              if uu____20304
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20309 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_81  ->
                                      FStar_Pervasives_Native.Some _0_81)
                                   uu____20309)
                               in
                            let uu____20312 = solve_prob orig guard [] wl  in
                            solve env uu____20312
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____20315,uu____20316)
                     ->
                     let head1 =
                       let uu____20320 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20320
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20364 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20364
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20406 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20406
                       then
                         let uu____20407 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20408 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20409 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20407 uu____20408 uu____20409
                       else ());
                      (let uu____20411 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20411
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20426 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20426
                          then
                            let guard =
                              let uu____20438 =
                                let uu____20439 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20439 = FStar_Syntax_Util.Equal  in
                              if uu____20438
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20443 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_82  ->
                                      FStar_Pervasives_Native.Some _0_82)
                                   uu____20443)
                               in
                            let uu____20446 = solve_prob orig guard [] wl  in
                            solve env uu____20446
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____20449,uu____20450) ->
                     let head1 =
                       let uu____20454 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20454
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20498 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20498
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20540 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20540
                       then
                         let uu____20541 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20542 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20543 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20541 uu____20542 uu____20543
                       else ());
                      (let uu____20545 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20545
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20560 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20560
                          then
                            let guard =
                              let uu____20572 =
                                let uu____20573 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20573 = FStar_Syntax_Util.Equal  in
                              if uu____20572
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20577 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_83  ->
                                      FStar_Pervasives_Native.Some _0_83)
                                   uu____20577)
                               in
                            let uu____20580 = solve_prob orig guard [] wl  in
                            solve env uu____20580
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____20583,uu____20584) ->
                     let head1 =
                       let uu____20602 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20602
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20646 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20646
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20688 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20688
                       then
                         let uu____20689 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20690 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20691 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20689 uu____20690 uu____20691
                       else ());
                      (let uu____20693 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20693
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20708 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20708
                          then
                            let guard =
                              let uu____20720 =
                                let uu____20721 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20721 = FStar_Syntax_Util.Equal  in
                              if uu____20720
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20725 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_84  ->
                                      FStar_Pervasives_Native.Some _0_84)
                                   uu____20725)
                               in
                            let uu____20728 = solve_prob orig guard [] wl  in
                            solve env uu____20728
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20731,FStar_Syntax_Syntax.Tm_match uu____20732) ->
                     let head1 =
                       let uu____20758 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20758
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20802 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20802
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20844 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20844
                       then
                         let uu____20845 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20846 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20847 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20845 uu____20846 uu____20847
                       else ());
                      (let uu____20849 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20849
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20864 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20864
                          then
                            let guard =
                              let uu____20876 =
                                let uu____20877 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20877 = FStar_Syntax_Util.Equal  in
                              if uu____20876
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20881 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_85  ->
                                      FStar_Pervasives_Native.Some _0_85)
                                   uu____20881)
                               in
                            let uu____20884 = solve_prob orig guard [] wl  in
                            solve env uu____20884
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20887,FStar_Syntax_Syntax.Tm_uinst uu____20888) ->
                     let head1 =
                       let uu____20898 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20898
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20942 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20942
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20984 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20984
                       then
                         let uu____20985 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20986 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20987 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20985 uu____20986 uu____20987
                       else ());
                      (let uu____20989 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20989
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21004 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21004
                          then
                            let guard =
                              let uu____21016 =
                                let uu____21017 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21017 = FStar_Syntax_Util.Equal  in
                              if uu____21016
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21021 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_86  ->
                                      FStar_Pervasives_Native.Some _0_86)
                                   uu____21021)
                               in
                            let uu____21024 = solve_prob orig guard [] wl  in
                            solve env uu____21024
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21027,FStar_Syntax_Syntax.Tm_name uu____21028) ->
                     let head1 =
                       let uu____21032 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21032
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21076 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21076
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21118 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21118
                       then
                         let uu____21119 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21120 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21121 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21119 uu____21120 uu____21121
                       else ());
                      (let uu____21123 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21123
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21138 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21138
                          then
                            let guard =
                              let uu____21150 =
                                let uu____21151 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21151 = FStar_Syntax_Util.Equal  in
                              if uu____21150
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21155 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_87  ->
                                      FStar_Pervasives_Native.Some _0_87)
                                   uu____21155)
                               in
                            let uu____21158 = solve_prob orig guard [] wl  in
                            solve env uu____21158
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21161,FStar_Syntax_Syntax.Tm_constant uu____21162)
                     ->
                     let head1 =
                       let uu____21166 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21166
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21210 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21210
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21252 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21252
                       then
                         let uu____21253 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21254 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21255 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21253 uu____21254 uu____21255
                       else ());
                      (let uu____21257 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21257
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21272 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21272
                          then
                            let guard =
                              let uu____21284 =
                                let uu____21285 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21285 = FStar_Syntax_Util.Equal  in
                              if uu____21284
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21289 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_88  ->
                                      FStar_Pervasives_Native.Some _0_88)
                                   uu____21289)
                               in
                            let uu____21292 = solve_prob orig guard [] wl  in
                            solve env uu____21292
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21295,FStar_Syntax_Syntax.Tm_fvar uu____21296) ->
                     let head1 =
                       let uu____21300 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21300
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21344 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21344
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21386 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21386
                       then
                         let uu____21387 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21388 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21389 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21387 uu____21388 uu____21389
                       else ());
                      (let uu____21391 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21391
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21406 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21406
                          then
                            let guard =
                              let uu____21418 =
                                let uu____21419 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21419 = FStar_Syntax_Util.Equal  in
                              if uu____21418
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21423 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_89  ->
                                      FStar_Pervasives_Native.Some _0_89)
                                   uu____21423)
                               in
                            let uu____21426 = solve_prob orig guard [] wl  in
                            solve env uu____21426
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21429,FStar_Syntax_Syntax.Tm_app uu____21430) ->
                     let head1 =
                       let uu____21448 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21448
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21492 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21492
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21534 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21534
                       then
                         let uu____21535 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21536 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21537 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21535 uu____21536 uu____21537
                       else ());
                      (let uu____21539 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21539
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21554 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21554
                          then
                            let guard =
                              let uu____21566 =
                                let uu____21567 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21567 = FStar_Syntax_Util.Equal  in
                              if uu____21566
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21571 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_90  ->
                                      FStar_Pervasives_Native.Some _0_90)
                                   uu____21571)
                               in
                            let uu____21574 = solve_prob orig guard [] wl  in
                            solve env uu____21574
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____21577,FStar_Syntax_Syntax.Tm_let uu____21578) ->
                     let uu____21603 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____21603
                     then
                       let uu____21604 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____21604
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____21606,uu____21607) ->
                     let uu____21620 =
                       let uu____21625 =
                         let uu____21626 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21627 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21628 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21629 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21626 uu____21627 uu____21628 uu____21629
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21625)
                        in
                     FStar_Errors.raise_error uu____21620
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____21630,FStar_Syntax_Syntax.Tm_let uu____21631) ->
                     let uu____21644 =
                       let uu____21649 =
                         let uu____21650 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21651 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21652 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21653 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21650 uu____21651 uu____21652 uu____21653
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21649)
                        in
                     FStar_Errors.raise_error uu____21644
                       t1.FStar_Syntax_Syntax.pos
                 | uu____21654 -> giveup env "head tag mismatch" orig)))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          let uu____21682 = p_scope orig  in
          mk_problem uu____21682 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____21691 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21691
           then
             let uu____21692 =
               let uu____21693 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____21693  in
             let uu____21694 =
               let uu____21695 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____21695  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____21692 uu____21694
           else ());
          (let uu____21697 =
             let uu____21698 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____21698  in
           if uu____21697
           then
             let uu____21699 =
               let uu____21700 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21701 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21700 uu____21701
                in
             giveup env uu____21699 orig
           else
             (let ret_sub_prob =
                let uu____21704 =
                  sub_prob c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                FStar_All.pipe_left
                  (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
                  uu____21704
                 in
              let arg_sub_probs =
                FStar_List.map2
                  (fun uu____21731  ->
                     fun uu____21732  ->
                       match (uu____21731, uu____21732) with
                       | ((a1,uu____21750),(a2,uu____21752)) ->
                           let uu____21761 =
                             sub_prob a1 FStar_TypeChecker_Common.EQ a2
                               "effect arg"
                              in
                           FStar_All.pipe_left
                             (fun _0_92  ->
                                FStar_TypeChecker_Common.TProb _0_92)
                             uu____21761)
                  c1_comp.FStar_Syntax_Syntax.effect_args
                  c2_comp.FStar_Syntax_Syntax.effect_args
                 in
              let sub_probs = ret_sub_prob :: arg_sub_probs  in
              let guard =
                let uu____21774 =
                  FStar_List.map
                    (fun p  ->
                       FStar_All.pipe_right (p_guard p)
                         FStar_Pervasives_Native.fst) sub_probs
                   in
                FStar_Syntax_Util.mk_conj_l uu____21774  in
              let wl1 =
                solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl
                 in
              solve env (attempt sub_probs wl1)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21798 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21805)::[] -> wp1
              | uu____21822 ->
                  let uu____21831 =
                    let uu____21832 =
                      let uu____21833 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____21833  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21832
                     in
                  failwith uu____21831
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21841 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21841]
              | x -> x  in
            let uu____21843 =
              let uu____21852 =
                let uu____21853 =
                  let uu____21854 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21854 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21853  in
              [uu____21852]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21843;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21855 = lift_c1 ()  in solve_eq uu____21855 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_21861  ->
                       match uu___117_21861 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21862 -> false))
                in
             let uu____21863 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21897)::uu____21898,(wp2,uu____21900)::uu____21901)
                   -> (wp1, wp2)
               | uu____21958 ->
                   let uu____21979 =
                     let uu____21984 =
                       let uu____21985 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21986 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21985 uu____21986
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21984)
                      in
                   FStar_Errors.raise_error uu____21979
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21863 with
             | (wpc1,wpc2) ->
                 let uu____22005 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____22005
                 then
                   let uu____22008 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____22008 wl
                 else
                   (let uu____22012 =
                      let uu____22019 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____22019  in
                    match uu____22012 with
                    | (c2_decl,qualifiers) ->
                        let uu____22040 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____22040
                        then
                          let c1_repr =
                            let uu____22044 =
                              let uu____22045 =
                                let uu____22046 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____22046  in
                              let uu____22047 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22045 uu____22047
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22044
                             in
                          let c2_repr =
                            let uu____22049 =
                              let uu____22050 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____22051 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22050 uu____22051
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22049
                             in
                          let prob =
                            let uu____22053 =
                              let uu____22058 =
                                let uu____22059 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____22060 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____22059
                                  uu____22060
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____22058
                               in
                            FStar_TypeChecker_Common.TProb uu____22053  in
                          let wl1 =
                            let uu____22062 =
                              let uu____22065 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____22065  in
                            solve_prob orig uu____22062 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____22074 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22074
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____22077 =
                                     let uu____22080 =
                                       let uu____22081 =
                                         let uu____22096 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____22097 =
                                           let uu____22100 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____22101 =
                                             let uu____22104 =
                                               let uu____22105 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____22105
                                                in
                                             [uu____22104]  in
                                           uu____22100 :: uu____22101  in
                                         (uu____22096, uu____22097)  in
                                       FStar_Syntax_Syntax.Tm_app uu____22081
                                        in
                                     FStar_Syntax_Syntax.mk uu____22080  in
                                   uu____22077 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____22114 =
                                    let uu____22117 =
                                      let uu____22118 =
                                        let uu____22133 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____22134 =
                                          let uu____22137 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____22138 =
                                            let uu____22141 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____22142 =
                                              let uu____22145 =
                                                let uu____22146 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____22146
                                                 in
                                              [uu____22145]  in
                                            uu____22141 :: uu____22142  in
                                          uu____22137 :: uu____22138  in
                                        (uu____22133, uu____22134)  in
                                      FStar_Syntax_Syntax.Tm_app uu____22118
                                       in
                                    FStar_Syntax_Syntax.mk uu____22117  in
                                  uu____22114 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____22153 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_93  ->
                                  FStar_TypeChecker_Common.TProb _0_93)
                               uu____22153
                              in
                           let wl1 =
                             let uu____22163 =
                               let uu____22166 =
                                 let uu____22169 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____22169 g  in
                               FStar_All.pipe_left
                                 (fun _0_94  ->
                                    FStar_Pervasives_Native.Some _0_94)
                                 uu____22166
                                in
                             solve_prob orig uu____22163 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____22182 = FStar_Util.physical_equality c1 c2  in
        if uu____22182
        then
          let uu____22183 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____22183
        else
          ((let uu____22186 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____22186
            then
              let uu____22187 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____22188 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____22187
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____22188
            else ());
           (let uu____22190 =
              let uu____22195 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____22196 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____22195, uu____22196)  in
            match uu____22190 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22200),FStar_Syntax_Syntax.Total
                    (t2,uu____22202)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____22219 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22219 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22222,FStar_Syntax_Syntax.Total uu____22223) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22241),FStar_Syntax_Syntax.Total
                    (t2,uu____22243)) ->
                     let uu____22260 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22260 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22264),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22266)) ->
                     let uu____22283 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22283 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22287),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22289)) ->
                     let uu____22306 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22306 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22309,FStar_Syntax_Syntax.Comp uu____22310) ->
                     let uu____22319 =
                       let uu___166_22324 = problem  in
                       let uu____22329 =
                         let uu____22330 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22330
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_22324.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22329;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_22324.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_22324.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_22324.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_22324.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_22324.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_22324.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_22324.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_22324.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22319 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____22331,FStar_Syntax_Syntax.Comp uu____22332) ->
                     let uu____22341 =
                       let uu___166_22346 = problem  in
                       let uu____22351 =
                         let uu____22352 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22352
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_22346.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22351;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_22346.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_22346.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_22346.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_22346.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_22346.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_22346.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_22346.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_22346.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22341 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22353,FStar_Syntax_Syntax.GTotal uu____22354) ->
                     let uu____22363 =
                       let uu___167_22368 = problem  in
                       let uu____22373 =
                         let uu____22374 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22374
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_22368.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_22368.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_22368.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22373;
                         FStar_TypeChecker_Common.element =
                           (uu___167_22368.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_22368.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_22368.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_22368.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_22368.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_22368.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22363 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22375,FStar_Syntax_Syntax.Total uu____22376) ->
                     let uu____22385 =
                       let uu___167_22390 = problem  in
                       let uu____22395 =
                         let uu____22396 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22396
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_22390.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_22390.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_22390.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22395;
                         FStar_TypeChecker_Common.element =
                           (uu___167_22390.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_22390.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_22390.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_22390.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_22390.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_22390.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22385 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22397,FStar_Syntax_Syntax.Comp uu____22398) ->
                     let uu____22399 =
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
                     if uu____22399
                     then
                       let uu____22400 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____22400 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____22406 =
                            let uu____22411 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____22411
                            then (c1_comp, c2_comp)
                            else
                              (let uu____22417 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____22418 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____22417, uu____22418))
                             in
                          match uu____22406 with
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
                           (let uu____22425 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____22425
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____22427 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____22427 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____22430 =
                                  let uu____22431 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____22432 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____22431 uu____22432
                                   in
                                giveup env uu____22430 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____22437 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____22475  ->
              match uu____22475 with
              | (uu____22488,uu____22489,u,uu____22491,uu____22492,uu____22493)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____22437 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____22524 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____22524 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____22542 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____22570  ->
                match uu____22570 with
                | (u1,u2) ->
                    let uu____22577 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____22578 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____22577 uu____22578))
         in
      FStar_All.pipe_right uu____22542 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____22595,[])) -> "{}"
      | uu____22620 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____22637 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____22637
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____22640 =
              FStar_List.map
                (fun uu____22650  ->
                   match uu____22650 with
                   | (uu____22655,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____22640 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____22660 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____22660 imps
  
let new_t_problem :
  'Auu____22668 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____22668 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____22668)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____22702 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____22702
                then
                  let uu____22703 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____22704 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22703
                    (rel_to_string rel) uu____22704
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
            let uu____22728 =
              let uu____22731 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_95  -> FStar_Pervasives_Native.Some _0_95)
                uu____22731
               in
            FStar_Syntax_Syntax.new_bv uu____22728 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____22740 =
              let uu____22743 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_96  -> FStar_Pervasives_Native.Some _0_96)
                uu____22743
               in
            let uu____22746 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____22740 uu____22746  in
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
          let uu____22776 = FStar_Options.eager_inference ()  in
          if uu____22776
          then
            let uu___168_22777 = probs  in
            {
              attempting = (uu___168_22777.attempting);
              wl_deferred = (uu___168_22777.wl_deferred);
              ctr = (uu___168_22777.ctr);
              defer_ok = false;
              smt_ok = (uu___168_22777.smt_ok);
              tcenv = (uu___168_22777.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22788 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22788
              then
                let uu____22789 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22789
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
          ((let uu____22803 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22803
            then
              let uu____22804 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22804
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22808 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22808
             then
               let uu____22809 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22809
             else ());
            (let f2 =
               let uu____22812 =
                 let uu____22813 = FStar_Syntax_Util.unmeta f1  in
                 uu____22813.FStar_Syntax_Syntax.n  in
               match uu____22812 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22817 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___169_22818 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___169_22818.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_22818.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_22818.FStar_TypeChecker_Env.implicits)
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
            let uu____22837 =
              let uu____22838 =
                let uu____22839 =
                  let uu____22840 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22840
                    (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22839;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22838  in
            FStar_All.pipe_left
              (fun _0_98  -> FStar_Pervasives_Native.Some _0_98) uu____22837
  
let with_guard_no_simp :
  'Auu____22867 .
    'Auu____22867 ->
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
            let uu____22887 =
              let uu____22888 =
                let uu____22889 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22889
                  (fun _0_99  -> FStar_TypeChecker_Common.NonTrivial _0_99)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22888;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22887
  
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
          (let uu____22927 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22927
           then
             let uu____22928 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22929 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22928
               uu____22929
           else ());
          (let prob =
             let uu____22932 =
               let uu____22937 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22937
                in
             FStar_All.pipe_left
               (fun _0_100  -> FStar_TypeChecker_Common.TProb _0_100)
               uu____22932
              in
           let g =
             let uu____22945 =
               let uu____22948 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22948
                 (fun uu____22950  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22945  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22968 = try_teq true env t1 t2  in
        match uu____22968 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22972 = FStar_TypeChecker_Env.get_range env  in
              let uu____22973 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22972 uu____22973);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22980 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22980
              then
                let uu____22981 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22982 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22983 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22981
                  uu____22982 uu____22983
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____22997 = FStar_TypeChecker_Env.get_range env  in
          let uu____22998 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22997 uu____22998
  
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
        (let uu____23017 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23017
         then
           let uu____23018 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____23019 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____23018 uu____23019
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let prob =
           let uu____23023 =
             let uu____23028 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____23028 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_101  -> FStar_TypeChecker_Common.CProb _0_101)
             uu____23023
            in
         let uu____23033 =
           let uu____23036 = singleton env prob  in
           solve_and_commit env uu____23036
             (fun uu____23038  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____23033)
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____23067  ->
        match uu____23067 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____23106 =
                 let uu____23111 =
                   let uu____23112 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____23113 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____23112 uu____23113
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____23111)  in
               let uu____23114 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____23106 uu____23114)
               in
            let equiv1 v1 v' =
              let uu____23122 =
                let uu____23127 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____23128 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____23127, uu____23128)  in
              match uu____23122 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____23147 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____23177 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____23177 with
                      | FStar_Syntax_Syntax.U_unif uu____23184 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____23213  ->
                                    match uu____23213 with
                                    | (u,v') ->
                                        let uu____23222 = equiv1 v1 v'  in
                                        if uu____23222
                                        then
                                          let uu____23225 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____23225 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____23241 -> []))
               in
            let uu____23246 =
              let wl =
                let uu___170_23250 = empty_worklist env  in
                {
                  attempting = (uu___170_23250.attempting);
                  wl_deferred = (uu___170_23250.wl_deferred);
                  ctr = (uu___170_23250.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_23250.smt_ok);
                  tcenv = (uu___170_23250.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____23268  ->
                      match uu____23268 with
                      | (lb,v1) ->
                          let uu____23275 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____23275 with
                           | USolved wl1 -> ()
                           | uu____23277 -> fail1 lb v1)))
               in
            let rec check_ineq uu____23285 =
              match uu____23285 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____23294) -> true
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
                      uu____23317,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____23319,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____23330) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____23337,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____23345 -> false)
               in
            let uu____23350 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____23365  ->
                      match uu____23365 with
                      | (u,v1) ->
                          let uu____23372 = check_ineq (u, v1)  in
                          if uu____23372
                          then true
                          else
                            ((let uu____23375 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____23375
                              then
                                let uu____23376 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____23377 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____23376
                                  uu____23377
                              else ());
                             false)))
               in
            if uu____23350
            then ()
            else
              ((let uu____23381 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____23381
                then
                  ((let uu____23383 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____23383);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____23393 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____23393))
                else ());
               (let uu____23403 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____23403))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit)
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
      let fail1 uu____23451 =
        match uu____23451 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____23465 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____23465
       then
         let uu____23466 = wl_to_string wl  in
         let uu____23467 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____23466 uu____23467
       else ());
      (let g1 =
         let uu____23482 = solve_and_commit env wl fail1  in
         match uu____23482 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___171_23495 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___171_23495.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_23495.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_23495.FStar_TypeChecker_Env.implicits)
             }
         | uu____23500 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___172_23504 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_23504.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_23504.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___172_23504.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____23530 = FStar_ST.op_Bang last_proof_ns  in
    match uu____23530 with
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
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
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
            let uu___173_23633 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___173_23633.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___173_23633.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___173_23633.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____23634 =
            let uu____23635 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____23635  in
          if uu____23634
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____23643 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____23644 =
                       let uu____23645 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____23645
                        in
                     FStar_Errors.diag uu____23643 uu____23644)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____23649 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____23650 =
                        let uu____23651 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____23651
                         in
                      FStar_Errors.diag uu____23649 uu____23650)
                   else ();
                   (let uu____23654 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____23654 "discharge_guard'"
                      env vc1);
                   (let uu____23655 = check_trivial vc1  in
                    match uu____23655 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____23662 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23663 =
                                let uu____23664 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____23664
                                 in
                              FStar_Errors.diag uu____23662 uu____23663)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____23669 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23670 =
                                let uu____23671 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____23671
                                 in
                              FStar_Errors.diag uu____23669 uu____23670)
                           else ();
                           (let vcs =
                              let uu____23682 = FStar_Options.use_tactics ()
                                 in
                              if uu____23682
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23702  ->
                                     (let uu____23704 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23704);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____23747  ->
                                              match uu____23747 with
                                              | (env1,goal,opts) ->
                                                  let uu____23763 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____23763, opts)))))
                              else
                                (let uu____23765 =
                                   let uu____23772 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23772)  in
                                 [uu____23765])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23805  ->
                                    match uu____23805 with
                                    | (env1,goal,opts) ->
                                        let uu____23815 = check_trivial goal
                                           in
                                        (match uu____23815 with
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
                                                (let uu____23823 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23824 =
                                                   let uu____23825 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____23826 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23825 uu____23826
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23823 uu____23824)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23829 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23830 =
                                                   let uu____23831 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23831
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23829 uu____23830)
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
      let uu____23841 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23841 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23847 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23847
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23854 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23854 with
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
          let uu____23873 = FStar_Syntax_Unionfind.find u  in
          match uu____23873 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23876 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23894 = acc  in
          match uu____23894 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23980 = hd1  in
                   (match uu____23980 with
                    | (uu____23993,env,u,tm,k,r) ->
                        let uu____23999 = unresolved u  in
                        if uu____23999
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___174_24029 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___174_24029.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___174_24029.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___174_24029.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___174_24029.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___174_24029.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___174_24029.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___174_24029.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___174_24029.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___174_24029.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___174_24029.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___174_24029.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___174_24029.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___174_24029.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___174_24029.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___174_24029.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___174_24029.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___174_24029.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___174_24029.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___174_24029.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___174_24029.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___174_24029.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___174_24029.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___174_24029.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___174_24029.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___174_24029.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___174_24029.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___174_24029.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___174_24029.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___174_24029.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___174_24029.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___174_24029.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___174_24029.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___174_24029.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___174_24029.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___174_24029.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___174_24029.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____24032 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____24032
                            then
                              let uu____24033 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____24034 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____24035 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____24033 uu____24034 uu____24035
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e when FStar_Errors.handleable e ->
                                  ((let uu____24046 =
                                      let uu____24055 =
                                        let uu____24062 =
                                          let uu____24063 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____24064 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____24063 uu____24064
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____24062, r)
                                         in
                                      [uu____24055]  in
                                    FStar_Errors.add_errors uu____24046);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___177_24078 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___177_24078.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___177_24078.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___177_24078.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____24081 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____24087  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____24081 with
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
        let uu___178_24115 = g  in
        let uu____24116 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___178_24115.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___178_24115.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___178_24115.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____24116
        }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____24170 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____24170 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____24183 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____24183
      | (reason,uu____24185,uu____24186,e,t,r)::uu____24190 ->
          let uu____24217 =
            let uu____24222 =
              let uu____24223 = FStar_Syntax_Print.term_to_string t  in
              let uu____24224 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____24223 uu____24224
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____24222)
             in
          FStar_Errors.raise_error uu____24217 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___179_24231 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_24231.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_24231.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_24231.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____24254 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24254 with
      | FStar_Pervasives_Native.Some uu____24259 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24269 = try_teq false env t1 t2  in
        match uu____24269 with
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
        (let uu____24289 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24289
         then
           let uu____24290 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____24291 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____24290
             uu____24291
         else ());
        (let uu____24293 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____24293 with
         | (prob,x) ->
             let g =
               let uu____24309 =
                 let uu____24312 = singleton' env prob true  in
                 solve_and_commit env uu____24312
                   (fun uu____24314  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____24309  in
             ((let uu____24324 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____24324
               then
                 let uu____24325 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____24326 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____24327 =
                   let uu____24328 = FStar_Util.must g  in
                   guard_to_string env uu____24328  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____24325 uu____24326 uu____24327
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
        let uu____24356 = check_subtyping env t1 t2  in
        match uu____24356 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____24375 =
              let uu____24376 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____24376 g  in
            FStar_Pervasives_Native.Some uu____24375
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24388 = check_subtyping env t1 t2  in
        match uu____24388 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____24407 =
              let uu____24408 =
                let uu____24409 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____24409]  in
              close_guard env uu____24408 g  in
            FStar_Pervasives_Native.Some uu____24407
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____24420 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24420
         then
           let uu____24421 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____24422 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____24421
             uu____24422
         else ());
        (let uu____24424 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____24424 with
         | (prob,x) ->
             let g =
               let uu____24434 =
                 let uu____24437 = singleton' env prob false  in
                 solve_and_commit env uu____24437
                   (fun uu____24439  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____24434  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____24450 =
                      let uu____24451 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____24451]  in
                    close_guard env uu____24450 g1  in
                  discharge_guard_nosmt env g2))
  