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
          let uu___116_91 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___116_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___116_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___116_91.FStar_TypeChecker_Env.implicits)
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
          let uu___117_199 = g  in
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
              (uu___117_199.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___117_199.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___117_199.FStar_TypeChecker_Env.implicits)
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
          let uu___118_242 = g  in
          let uu____243 =
            let uu____244 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____244  in
          {
            FStar_TypeChecker_Env.guard_f = uu____243;
            FStar_TypeChecker_Env.deferred =
              (uu___118_242.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_242.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_242.FStar_TypeChecker_Env.implicits)
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
            let uu___119_368 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___119_368.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___119_368.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___119_368.FStar_TypeChecker_Env.implicits)
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
            let uu___120_400 = g  in
            let uu____401 =
              let uu____402 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____402  in
            {
              FStar_TypeChecker_Env.guard_f = uu____401;
              FStar_TypeChecker_Env.deferred =
                (uu___120_400.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___120_400.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___120_400.FStar_TypeChecker_Env.implicits)
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
  fun uu___86_808  ->
    match uu___86_808 with
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
    fun uu___87_905  ->
      match uu___87_905 with
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
    fun uu___88_939  ->
      match uu___88_939 with
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
        let uu___121_1059 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___121_1059.wl_deferred);
          ctr = (uu___121_1059.ctr);
          defer_ok = (uu___121_1059.defer_ok);
          smt_ok;
          tcenv = (uu___121_1059.tcenv)
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
      let uu___122_1090 = empty_worklist env  in
      let uu____1091 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1091;
        wl_deferred = (uu___122_1090.wl_deferred);
        ctr = (uu___122_1090.ctr);
        defer_ok = false;
        smt_ok = (uu___122_1090.smt_ok);
        tcenv = (uu___122_1090.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___123_1105 = wl  in
        {
          attempting = (uu___123_1105.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___123_1105.ctr);
          defer_ok = (uu___123_1105.defer_ok);
          smt_ok = (uu___123_1105.smt_ok);
          tcenv = (uu___123_1105.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___124_1122 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___124_1122.wl_deferred);
        ctr = (uu___124_1122.ctr);
        defer_ok = (uu___124_1122.defer_ok);
        smt_ok = (uu___124_1122.smt_ok);
        tcenv = (uu___124_1122.tcenv)
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
  fun uu___89_1138  ->
    match uu___89_1138 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1142 'Auu____1143 .
    ('Auu____1142,'Auu____1143) FStar_TypeChecker_Common.problem ->
      ('Auu____1142,'Auu____1143) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___125_1160 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___125_1160.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___125_1160.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___125_1160.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___125_1160.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___125_1160.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___125_1160.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___125_1160.FStar_TypeChecker_Common.rank)
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
  fun uu___90_1189  ->
    match uu___90_1189 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___91_1213  ->
      match uu___91_1213 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___92_1216  ->
    match uu___92_1216 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___93_1229  ->
    match uu___93_1229 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___94_1244  ->
    match uu___94_1244 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___95_1259  ->
    match uu___95_1259 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___96_1276  ->
    match uu___96_1276 with
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
  fun uu___97_1480  ->
    match uu___97_1480 with
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
         (fun uu___98_1844  ->
            match uu___98_1844 with
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
        (fun uu___99_1879  ->
           match uu___99_1879 with
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
        (fun uu___100_1914  ->
           match uu___100_1914 with
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
                    let uu___126_2006 = x  in
                    let uu____2007 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___126_2006.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___126_2006.FStar_Syntax_Syntax.index);
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
          | FStar_Syntax_Syntax.Tm_uvar uu____2556 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2587 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2614 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2651 ->
              let uu____2658 =
                let uu____2659 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2660 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2659 uu____2660
                 in
              failwith uu____2658
          | FStar_Syntax_Syntax.Tm_ascribed uu____2675 ->
              let uu____2702 =
                let uu____2703 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2704 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2703 uu____2704
                 in
              failwith uu____2702
          | FStar_Syntax_Syntax.Tm_delayed uu____2719 ->
              let uu____2744 =
                let uu____2745 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2746 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2745 uu____2746
                 in
              failwith uu____2744
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2761 =
                let uu____2762 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2763 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2762 uu____2763
                 in
              failwith uu____2761
           in
        let uu____2778 = whnf env t1  in aux false uu____2778
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____2800 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2800 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2823 = base_and_refinement env t  in
      FStar_All.pipe_right uu____2823 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2857 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2857, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____2863 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2863 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2884 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____2884 with
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
  fun uu____2963  ->
    match uu____2963 with
    | (t_base,refopt) ->
        let uu____2990 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____2990 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3022 =
      let uu____3025 =
        let uu____3028 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3051  ->
                  match uu____3051 with | (uu____3058,uu____3059,x) -> x))
           in
        FStar_List.append wl.attempting uu____3028  in
      FStar_List.map (wl_prob_to_string wl) uu____3025  in
    FStar_All.pipe_right uu____3022 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3072 =
          let uu____3085 =
            let uu____3086 = FStar_Syntax_Subst.compress k  in
            uu____3086.FStar_Syntax_Syntax.n  in
          match uu____3085 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3139 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3139)
              else
                (let uu____3153 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3153 with
                 | (ys',t1,uu____3176) ->
                     let uu____3181 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3181))
          | uu____3222 ->
              let uu____3223 =
                let uu____3234 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3234)  in
              ((ys, t), uu____3223)
           in
        match uu____3072 with
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
                 let uu____3283 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3283 c  in
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
             let uu____3312 = p_guard prob  in
             match uu____3312 with
             | (uu____3317,uv) ->
                 ((let uu____3320 =
                     let uu____3321 = FStar_Syntax_Subst.compress uv  in
                     uu____3321.FStar_Syntax_Syntax.n  in
                   match uu____3320 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                       let bs = p_scope prob  in
                       let phi1 = u_abs k bs phi  in
                       ((let uu____3353 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3353
                         then
                           let uu____3354 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____3355 =
                             FStar_Syntax_Print.term_to_string uv  in
                           let uu____3356 =
                             FStar_Syntax_Print.term_to_string phi1  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3354
                             uu____3355 uu____3356
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3359 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___127_3362 = wl  in
                   {
                     attempting = (uu___127_3362.attempting);
                     wl_deferred = (uu___127_3362.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___127_3362.defer_ok);
                     smt_ok = (uu___127_3362.smt_ok);
                     tcenv = (uu___127_3362.tcenv)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3377 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3377
         then
           let uu____3378 = FStar_Util.string_of_int pid  in
           let uu____3379 =
             let uu____3380 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3380 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3378 uu____3379
         else ());
        commit sol;
        (let uu___128_3387 = wl  in
         {
           attempting = (uu___128_3387.attempting);
           wl_deferred = (uu___128_3387.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___128_3387.defer_ok);
           smt_ok = (uu___128_3387.smt_ok);
           tcenv = (uu___128_3387.tcenv)
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
             | (uu____3427,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3439 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____3439
              in
           (let uu____3445 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3445
            then
              let uu____3446 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3447 =
                let uu____3448 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3448 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3446 uu____3447
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
        let uu____3480 =
          let uu____3487 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3487 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3480
          (FStar_Util.for_some
             (fun uu____3523  ->
                match uu____3523 with
                | (uv,uu____3529) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3536 'Auu____3537 .
    'Auu____3536 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3537)
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
            let uu____3569 = occurs wl uk t  in Prims.op_Negation uu____3569
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3576 =
                 let uu____3577 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____3578 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3577 uu____3578
                  in
               FStar_Pervasives_Native.Some uu____3576)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____3588 'Auu____3589 .
    'Auu____3588 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3589)
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
            let uu____3643 = occurs_check env wl uk t  in
            match uu____3643 with
            | (occurs_ok,msg) ->
                let uu____3674 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3674, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____3697 'Auu____3698 .
    (FStar_Syntax_Syntax.bv,'Auu____3697) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3698) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3698) FStar_Pervasives_Native.tuple2
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
      let uu____3782 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3836  ->
                fun uu____3837  ->
                  match (uu____3836, uu____3837) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3918 =
                        let uu____3919 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____3919  in
                      if uu____3918
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____3944 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____3944
                         then
                           let uu____3957 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____3957)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____3782 with | (isect,uu____3998) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4023 'Auu____4024 .
    (FStar_Syntax_Syntax.bv,'Auu____4023) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4024) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4079  ->
              fun uu____4080  ->
                match (uu____4079, uu____4080) with
                | ((a,uu____4098),(b,uu____4100)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4114 'Auu____4115 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4114) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4115)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4115)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4166 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4180  ->
                      match uu____4180 with
                      | (b,uu____4186) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4166
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4202 -> FStar_Pervasives_Native.None
  
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
            let uu____4275 = pat_var_opt env seen hd1  in
            (match uu____4275 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4289 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4289
                   then
                     let uu____4290 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4290
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4308 =
      let uu____4309 = FStar_Syntax_Subst.compress t  in
      uu____4309.FStar_Syntax_Syntax.n  in
    match uu____4308 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4312 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4329;
           FStar_Syntax_Syntax.pos = uu____4330;
           FStar_Syntax_Syntax.vars = uu____4331;_},uu____4332)
        -> true
    | uu____4369 -> false
  
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
           FStar_Syntax_Syntax.pos = uu____4493;
           FStar_Syntax_Syntax.vars = uu____4494;_},args)
        -> (t, uv, k, args)
    | uu____4562 -> failwith "Not a flex-uvar"
  
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
      let uu____4639 = destruct_flex_t t  in
      match uu____4639 with
      | (t1,uv,k,args) ->
          let uu____4754 = pat_vars env [] args  in
          (match uu____4754 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4852 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4933 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4968 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4972 -> false
  
let string_of_option :
  'Auu____4976 .
    ('Auu____4976 -> Prims.string) ->
      'Auu____4976 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___101_4989  ->
      match uu___101_4989 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____4995 = f x  in Prims.strcat "Some " uu____4995
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___102_4998  ->
    match uu___102_4998 with
    | MisMatch (d1,d2) ->
        let uu____5009 =
          let uu____5010 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5011 =
            let uu____5012 =
              let uu____5013 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5013 ")"  in
            Prims.strcat ") (" uu____5012  in
          Prims.strcat uu____5010 uu____5011  in
        Prims.strcat "MisMatch (" uu____5009
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___103_5016  ->
    match uu___103_5016 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5031 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5057 = m2 ()  in
          (match uu____5057 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5072 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5081 ->
          let uu____5082 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5082 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5093 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5112 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5121 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5149 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5149
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5150 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5151 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5152 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5169 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5182 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5206) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5212,uu____5213) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5255) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5276;
             FStar_Syntax_Syntax.index = uu____5277;
             FStar_Syntax_Syntax.sort = t2;_},uu____5279)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5286 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5287 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5288 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5301 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5319 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5319
  
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
            let uu____5340 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5340
            then FullMatch
            else
              (let uu____5342 =
                 let uu____5351 =
                   let uu____5354 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5354  in
                 let uu____5355 =
                   let uu____5358 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5358  in
                 (uu____5351, uu____5355)  in
               MisMatch uu____5342)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5364),FStar_Syntax_Syntax.Tm_uinst (g,uu____5366)) ->
            let uu____5375 = head_matches env f g  in
            FStar_All.pipe_right uu____5375 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5378 = FStar_Const.eq_const c d  in
            if uu____5378
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5385),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5387)) ->
            let uu____5436 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5436
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5443),FStar_Syntax_Syntax.Tm_refine (y,uu____5445)) ->
            let uu____5454 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5454 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5456),uu____5457) ->
            let uu____5462 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5462 head_match
        | (uu____5463,FStar_Syntax_Syntax.Tm_refine (x,uu____5465)) ->
            let uu____5470 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5470 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5471,FStar_Syntax_Syntax.Tm_type
           uu____5472) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5473,FStar_Syntax_Syntax.Tm_arrow uu____5474) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           uu____5499,FStar_Syntax_Syntax.Tm_match uu____5500) ->
            ((let uu____5546 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelDelta")
                 in
              if uu____5546
              then
                FStar_ST.op_Colon_Equals FStar_Syntax_Util.debug_term_eq true
              else ());
             (let uu____5567 = FStar_Syntax_Util.term_eq t11 t21  in
              if uu____5567
              then FullMatch
              else
                MisMatch
                  (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None)))
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5574),FStar_Syntax_Syntax.Tm_app (head',uu____5576))
            ->
            let uu____5617 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5617 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5619),uu____5620) ->
            let uu____5641 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5641 head_match
        | (uu____5642,FStar_Syntax_Syntax.Tm_app (head1,uu____5644)) ->
            let uu____5665 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5665 head_match
        | uu____5666 ->
            let uu____5671 =
              let uu____5680 = delta_depth_of_term env t11  in
              let uu____5683 = delta_depth_of_term env t21  in
              (uu____5680, uu____5683)  in
            MisMatch uu____5671
  
let head_matches_delta :
  'Auu____5695 .
    FStar_TypeChecker_Env.env ->
      'Auu____5695 ->
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
            let uu____5728 = FStar_Syntax_Util.head_and_args t  in
            match uu____5728 with
            | (head1,uu____5746) ->
                let uu____5767 =
                  let uu____5768 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5768.FStar_Syntax_Syntax.n  in
                (match uu____5767 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5774 =
                       let uu____5775 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5775 FStar_Option.isSome
                        in
                     if uu____5774
                     then
                       let uu____5794 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____5794
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5798 -> FStar_Pervasives_Native.None)
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5901)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____5919 =
                     let uu____5928 = maybe_inline t11  in
                     let uu____5931 = maybe_inline t21  in
                     (uu____5928, uu____5931)  in
                   match uu____5919 with
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
                (uu____5968,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____5986 =
                     let uu____5995 = maybe_inline t11  in
                     let uu____5998 = maybe_inline t21  in
                     (uu____5995, uu____5998)  in
                   match uu____5986 with
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
                let uu____6041 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6041 with
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
                let uu____6064 =
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
                (match uu____6064 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6088 -> fail1 r
            | uu____6097 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6110 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6110
           then
             let uu____6111 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6112 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6113 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6111
               uu____6112 uu____6113
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6153 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6189 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___104_6201  ->
    match uu___104_6201 with
    | T (t,uu____6203) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6219 = FStar_Syntax_Util.type_u ()  in
      match uu____6219 with
      | (t,uu____6225) ->
          let uu____6226 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6226
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6237 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6237 FStar_Pervasives_Native.fst
  
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
        let uu____6301 = head_matches env t1 t'  in
        match uu____6301 with
        | MisMatch uu____6302 -> false
        | uu____6311 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6407,imp),T (t2,uu____6410)) -> (t2, imp)
                     | uu____6429 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6496  ->
                    match uu____6496 with
                    | (t2,uu____6510) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6553 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6553 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6628))::tcs2) ->
                       aux
                         (((let uu___129_6663 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_6663.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_6663.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6681 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___105_6734 =
                 match uu___105_6734 with
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
               let uu____6851 = decompose1 [] bs1  in
               (rebuild, matches, uu____6851))
      | uu____6900 ->
          let rebuild uu___106_6906 =
            match uu___106_6906 with
            | [] -> t1
            | uu____6909 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___107_6940  ->
    match uu___107_6940 with
    | T (t,uu____6942) -> t
    | uu____6951 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___108_6954  ->
    match uu___108_6954 with
    | T (t,uu____6956) -> FStar_Syntax_Syntax.as_arg t
    | uu____6965 -> failwith "Impossible"
  
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
              | (uu____7081,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7106 = new_uvar r scope1 k  in
                  (match uu____7106 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7124 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7141 =
                         let uu____7142 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7142
                          in
                       ((T (gi_xs, mk_kind)), uu____7141))
              | (uu____7155,uu____7156,C uu____7157) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7304 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7321;
                         FStar_Syntax_Syntax.vars = uu____7322;_})
                        ->
                        let uu____7345 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7345 with
                         | (T (gi_xs,uu____7369),prob) ->
                             let uu____7379 =
                               let uu____7380 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7380
                                in
                             (uu____7379, [prob])
                         | uu____7383 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7398;
                         FStar_Syntax_Syntax.vars = uu____7399;_})
                        ->
                        let uu____7422 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7422 with
                         | (T (gi_xs,uu____7446),prob) ->
                             let uu____7456 =
                               let uu____7457 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7457
                                in
                             (uu____7456, [prob])
                         | uu____7460 -> failwith "impossible")
                    | (uu____7471,uu____7472,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7474;
                         FStar_Syntax_Syntax.vars = uu____7475;_})
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
                        let uu____7606 =
                          let uu____7615 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7615 FStar_List.unzip
                           in
                        (match uu____7606 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7669 =
                                 let uu____7670 =
                                   let uu____7673 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7673 un_T  in
                                 let uu____7674 =
                                   let uu____7683 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7683
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7670;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7674;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7669
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7692 ->
                        let uu____7705 = sub_prob scope1 args q  in
                        (match uu____7705 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7304 with
                   | (tc,probs) ->
                       let uu____7736 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7799,uu____7800),T
                            (t,uu____7802)) ->
                             let b1 =
                               ((let uu___130_7839 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_7839.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_7839.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7840 =
                               let uu____7847 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7847 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7840)
                         | uu____7882 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7736 with
                        | (bopt,scope2,args1) ->
                            let uu____7966 = aux scope2 args1 qs2  in
                            (match uu____7966 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8004 =
                                           let uu____8007 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8007  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8004
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
                                         let uu____8032 =
                                           let uu____8035 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8036 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8035 :: uu____8036  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8032
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
  'Auu____8105 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8105)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8105)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___131_8126 = p  in
      let uu____8131 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8132 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___131_8126.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8131;
        FStar_TypeChecker_Common.relation =
          (uu___131_8126.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8132;
        FStar_TypeChecker_Common.element =
          (uu___131_8126.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___131_8126.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___131_8126.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___131_8126.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___131_8126.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___131_8126.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8144 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8144
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8153 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8173 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8173 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8183 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8183 with
           | (lh,uu____8203) ->
               let uu____8224 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8224 with
                | (rh,uu____8244) ->
                    let uu____8265 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8282,FStar_Syntax_Syntax.Tm_uvar uu____8283)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8320,uu____8321)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8342,FStar_Syntax_Syntax.Tm_uvar uu____8343)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8364,uu____8365)
                          ->
                          let uu____8382 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8382 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8431 ->
                                    let rank =
                                      let uu____8439 = is_top_level_prob prob
                                         in
                                      if uu____8439
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8441 =
                                      let uu___132_8446 = tp  in
                                      let uu____8451 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___132_8446.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___132_8446.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___132_8446.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8451;
                                        FStar_TypeChecker_Common.element =
                                          (uu___132_8446.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___132_8446.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___132_8446.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___132_8446.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___132_8446.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___132_8446.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8441)))
                      | (uu____8462,FStar_Syntax_Syntax.Tm_uvar uu____8463)
                          ->
                          let uu____8480 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8480 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8529 ->
                                    let uu____8536 =
                                      let uu___133_8543 = tp  in
                                      let uu____8548 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___133_8543.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8548;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___133_8543.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___133_8543.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___133_8543.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___133_8543.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___133_8543.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___133_8543.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___133_8543.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___133_8543.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8536)))
                      | (uu____8565,uu____8566) -> (rigid_rigid, tp)  in
                    (match uu____8265 with
                     | (rank,tp1) ->
                         let uu____8585 =
                           FStar_All.pipe_right
                             (let uu___134_8591 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___134_8591.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___134_8591.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___134_8591.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___134_8591.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___134_8591.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___134_8591.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___134_8591.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___134_8591.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___134_8591.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8585))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8601 =
            FStar_All.pipe_right
              (let uu___135_8607 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___135_8607.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___135_8607.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___135_8607.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___135_8607.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___135_8607.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___135_8607.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___135_8607.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___135_8607.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___135_8607.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8601)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8662 probs =
      match uu____8662 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8715 = rank wl hd1  in
               (match uu____8715 with
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
    match projectee with | UDeferred _0 -> true | uu____8822 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8834 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8846 -> false
  
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
                        let uu____8886 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8886 with
                        | (k,uu____8892) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8902 -> false)))
            | uu____8903 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8951 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8957 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8957 = (Prims.parse_int "0")))
                           in
                        if uu____8951 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8971 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8977 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8977 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8971)
               in
            let uu____8978 = filter1 u12  in
            let uu____8981 = filter1 u22  in (uu____8978, uu____8981)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9004 = filter_out_common_univs us1 us2  in
                (match uu____9004 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9057 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9057 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9060 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9070 =
                          let uu____9071 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9072 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9071
                            uu____9072
                           in
                        UFailed uu____9070))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9092 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9092 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9114 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9114 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9117 ->
                let uu____9122 =
                  let uu____9123 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9124 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9123
                    uu____9124 msg
                   in
                UFailed uu____9122
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9125,uu____9126) ->
              let uu____9127 =
                let uu____9128 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9129 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9128 uu____9129
                 in
              failwith uu____9127
          | (FStar_Syntax_Syntax.U_unknown ,uu____9130) ->
              let uu____9131 =
                let uu____9132 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9133 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9132 uu____9133
                 in
              failwith uu____9131
          | (uu____9134,FStar_Syntax_Syntax.U_bvar uu____9135) ->
              let uu____9136 =
                let uu____9137 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9138 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9137 uu____9138
                 in
              failwith uu____9136
          | (uu____9139,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9140 =
                let uu____9141 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9142 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9141 uu____9142
                 in
              failwith uu____9140
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9166 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9166
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9188 = occurs_univ v1 u3  in
              if uu____9188
              then
                let uu____9189 =
                  let uu____9190 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9191 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9190 uu____9191
                   in
                try_umax_components u11 u21 uu____9189
              else
                (let uu____9193 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9193)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9213 = occurs_univ v1 u3  in
              if uu____9213
              then
                let uu____9214 =
                  let uu____9215 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9216 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9215 uu____9216
                   in
                try_umax_components u11 u21 uu____9214
              else
                (let uu____9218 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9218)
          | (FStar_Syntax_Syntax.U_max uu____9227,uu____9228) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9234 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9234
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9236,FStar_Syntax_Syntax.U_max uu____9237) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9243 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9243
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9245,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9246,FStar_Syntax_Syntax.U_name
             uu____9247) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9248) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9249) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9250,FStar_Syntax_Syntax.U_succ
             uu____9251) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9252,FStar_Syntax_Syntax.U_zero
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
      let uu____9338 = bc1  in
      match uu____9338 with
      | (bs1,mk_cod1) ->
          let uu____9379 = bc2  in
          (match uu____9379 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9483 = aux xs ys  in
                     (match uu____9483 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9566 =
                       let uu____9573 = mk_cod1 xs  in ([], uu____9573)  in
                     let uu____9576 =
                       let uu____9583 = mk_cod2 ys  in ([], uu____9583)  in
                     (uu____9566, uu____9576)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9694 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9694
       then
         let uu____9695 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9695
       else ());
      (let uu____9697 = next_prob probs  in
       match uu____9697 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___136_9718 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___136_9718.wl_deferred);
               ctr = (uu___136_9718.ctr);
               defer_ok = (uu___136_9718.defer_ok);
               smt_ok = (uu___136_9718.smt_ok);
               tcenv = (uu___136_9718.tcenv)
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
                  let uu____9729 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9729 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9734 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9734 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9739,uu____9740) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9757 ->
                let uu____9766 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9825  ->
                          match uu____9825 with
                          | (c,uu____9833,uu____9834) -> c < probs.ctr))
                   in
                (match uu____9766 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9875 =
                            FStar_List.map
                              (fun uu____9890  ->
                                 match uu____9890 with
                                 | (uu____9901,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9875
                      | uu____9904 ->
                          let uu____9913 =
                            let uu___137_9914 = probs  in
                            let uu____9915 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9936  ->
                                      match uu____9936 with
                                      | (uu____9943,uu____9944,y) -> y))
                               in
                            {
                              attempting = uu____9915;
                              wl_deferred = rest;
                              ctr = (uu___137_9914.ctr);
                              defer_ok = (uu___137_9914.defer_ok);
                              smt_ok = (uu___137_9914.smt_ok);
                              tcenv = (uu___137_9914.tcenv)
                            }  in
                          solve env uu____9913))))

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
            let uu____9951 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9951 with
            | USolved wl1 ->
                let uu____9953 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9953
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
                  let uu____9999 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9999 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10002 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10014;
                  FStar_Syntax_Syntax.vars = uu____10015;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10018;
                  FStar_Syntax_Syntax.vars = uu____10019;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10033,uu____10034) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10041,FStar_Syntax_Syntax.Tm_uinst uu____10042) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10049 -> USolved wl

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
            ((let uu____10059 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10059
              then
                let uu____10060 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10060 msg
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
        (let uu____10069 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10069
         then
           let uu____10070 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10070
         else ());
        (let uu____10072 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10072 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10134 = head_matches_delta env () t1 t2  in
               match uu____10134 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10175 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10224 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10239 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10240 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10239, uu____10240)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10245 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10246 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10245, uu____10246)
                           in
                        (match uu____10224 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10272 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10272
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10303 =
                                    let uu____10312 =
                                      let uu____10315 =
                                        let uu____10318 =
                                          let uu____10319 =
                                            let uu____10326 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10326)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10319
                                           in
                                        FStar_Syntax_Syntax.mk uu____10318
                                         in
                                      uu____10315
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10334 =
                                      let uu____10337 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10337]  in
                                    (uu____10312, uu____10334)  in
                                  FStar_Pervasives_Native.Some uu____10303
                              | (uu____10350,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10352)) ->
                                  let uu____10357 =
                                    let uu____10364 =
                                      let uu____10367 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10367]  in
                                    (t11, uu____10364)  in
                                  FStar_Pervasives_Native.Some uu____10357
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10377),uu____10378) ->
                                  let uu____10383 =
                                    let uu____10390 =
                                      let uu____10393 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10393]  in
                                    (t21, uu____10390)  in
                                  FStar_Pervasives_Native.Some uu____10383
                              | uu____10402 ->
                                  let uu____10407 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10407 with
                                   | (head1,uu____10431) ->
                                       let uu____10452 =
                                         let uu____10453 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10453.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10452 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10464;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10466;_}
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
                                        | uu____10473 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10486) ->
                  let uu____10511 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___109_10537  ->
                            match uu___109_10537 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10544 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10544 with
                                      | (u',uu____10560) ->
                                          let uu____10581 =
                                            let uu____10582 = whnf env u'  in
                                            uu____10582.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10581 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10586) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10611 -> false))
                                 | uu____10612 -> false)
                            | uu____10615 -> false))
                     in
                  (match uu____10511 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10649 tps =
                         match uu____10649 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10697 =
                                    let uu____10706 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10706  in
                                  (match uu____10697 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10741 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10750 =
                         let uu____10759 =
                           let uu____10766 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10766, [])  in
                         make_lower_bound uu____10759 lower_bounds  in
                       (match uu____10750 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10778 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10778
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
                            ((let uu____10798 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10798
                              then
                                let wl' =
                                  let uu___138_10800 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___138_10800.wl_deferred);
                                    ctr = (uu___138_10800.ctr);
                                    defer_ok = (uu___138_10800.defer_ok);
                                    smt_ok = (uu___138_10800.smt_ok);
                                    tcenv = (uu___138_10800.tcenv)
                                  }  in
                                let uu____10801 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10801
                              else ());
                             (let uu____10803 =
                                solve_t env eq_prob
                                  (let uu___139_10805 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___139_10805.wl_deferred);
                                     ctr = (uu___139_10805.ctr);
                                     defer_ok = (uu___139_10805.defer_ok);
                                     smt_ok = (uu___139_10805.smt_ok);
                                     tcenv = (uu___139_10805.tcenv)
                                   })
                                 in
                              match uu____10803 with
                              | Success uu____10808 ->
                                  let wl1 =
                                    let uu___140_10810 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___140_10810.wl_deferred);
                                      ctr = (uu___140_10810.ctr);
                                      defer_ok = (uu___140_10810.defer_ok);
                                      smt_ok = (uu___140_10810.smt_ok);
                                      tcenv = (uu___140_10810.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10812 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10817 -> FStar_Pervasives_Native.None))))
              | uu____10818 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10827 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10827
         then
           let uu____10828 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10828
         else ());
        (let uu____10830 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10830 with
         | (u,args) ->
             let uu____10869 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10869 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10910 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10910 with
                    | (h1,args1) ->
                        let uu____10951 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____10951 with
                         | (h2,uu____10971) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10998 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____10998
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11016 =
                                          let uu____11019 =
                                            let uu____11020 =
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
                                                   _0_53) uu____11020
                                             in
                                          [uu____11019]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11016))
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
                                       (let uu____11053 =
                                          let uu____11056 =
                                            let uu____11057 =
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
                                                   _0_54) uu____11057
                                             in
                                          [uu____11056]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11053))
                                  else FStar_Pervasives_Native.None
                              | uu____11071 -> FStar_Pervasives_Native.None))
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
                             let uu____11161 =
                               let uu____11170 =
                                 let uu____11173 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11173  in
                               (uu____11170, m1)  in
                             FStar_Pervasives_Native.Some uu____11161)
                    | (uu____11186,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11188)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11236),uu____11237) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11284 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11337) ->
                       let uu____11362 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___110_11388  ->
                                 match uu___110_11388 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11395 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11395 with
                                           | (u',uu____11411) ->
                                               let uu____11432 =
                                                 let uu____11433 =
                                                   whnf env u'  in
                                                 uu____11433.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11432 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11437) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11462 -> false))
                                      | uu____11463 -> false)
                                 | uu____11466 -> false))
                          in
                       (match uu____11362 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11504 tps =
                              match uu____11504 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11566 =
                                         let uu____11577 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11577  in
                                       (match uu____11566 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11628 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11639 =
                              let uu____11650 =
                                let uu____11659 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11659, [])  in
                              make_upper_bound uu____11650 upper_bounds  in
                            (match uu____11639 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11673 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11673
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
                                 ((let uu____11699 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11699
                                   then
                                     let wl' =
                                       let uu___141_11701 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___141_11701.wl_deferred);
                                         ctr = (uu___141_11701.ctr);
                                         defer_ok = (uu___141_11701.defer_ok);
                                         smt_ok = (uu___141_11701.smt_ok);
                                         tcenv = (uu___141_11701.tcenv)
                                       }  in
                                     let uu____11702 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11702
                                   else ());
                                  (let uu____11704 =
                                     solve_t env eq_prob
                                       (let uu___142_11706 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___142_11706.wl_deferred);
                                          ctr = (uu___142_11706.ctr);
                                          defer_ok =
                                            (uu___142_11706.defer_ok);
                                          smt_ok = (uu___142_11706.smt_ok);
                                          tcenv = (uu___142_11706.tcenv)
                                        })
                                      in
                                   match uu____11704 with
                                   | Success uu____11709 ->
                                       let wl1 =
                                         let uu___143_11711 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___143_11711.wl_deferred);
                                           ctr = (uu___143_11711.ctr);
                                           defer_ok =
                                             (uu___143_11711.defer_ok);
                                           smt_ok = (uu___143_11711.smt_ok);
                                           tcenv = (uu___143_11711.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11713 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11718 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11719 -> failwith "Impossible: Not a flex-rigid")))

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
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs scope env1 subst1  in
                    ((let uu____11794 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11794
                      then
                        let uu____11795 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11795
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___144_11849 = hd1  in
                      let uu____11850 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_11849.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_11849.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11850
                      }  in
                    let hd21 =
                      let uu___145_11854 = hd2  in
                      let uu____11855 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_11854.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_11854.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11855
                      }  in
                    let prob =
                      let uu____11859 =
                        let uu____11864 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11864 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11859
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____11875 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11875
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____11879 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____11879 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11917 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____11922 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____11917 uu____11922
                            in
                         ((let uu____11932 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____11932
                           then
                             let uu____11933 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11934 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11933 uu____11934
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail1 -> fail1)
                | uu____11957 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____11967 = aux scope env [] bs1 bs2  in
              match uu____11967 with
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
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____11992 = compress_tprob wl problem  in
         solve_t' env uu____11992 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12026 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12026 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12057,uu____12058) ->
                    let rec may_relate head3 =
                      let uu____12083 =
                        let uu____12084 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12084.FStar_Syntax_Syntax.n  in
                      match uu____12083 with
                      | FStar_Syntax_Syntax.Tm_name uu____12087 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12088 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12111;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____12112;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12115;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12116;
                            FStar_Syntax_Syntax.fv_qual = uu____12117;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12121,uu____12122) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12164) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12170) ->
                          may_relate t
                      | uu____12175 -> false  in
                    let uu____12176 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12176
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
                                 let uu____12193 =
                                   let uu____12194 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12194 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12193
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____12196 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____12196
                    else
                      (let uu____12198 =
                         let uu____12199 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12200 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12199 uu____12200
                          in
                       giveup env1 uu____12198 orig)
                | (uu____12201,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___146_12215 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___146_12215.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___146_12215.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___146_12215.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___146_12215.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___146_12215.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___146_12215.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___146_12215.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___146_12215.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12216,FStar_Pervasives_Native.None ) ->
                    ((let uu____12228 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12228
                      then
                        let uu____12229 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12230 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12231 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12232 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12229
                          uu____12230 uu____12231 uu____12232
                      else ());
                     (let uu____12234 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12234 with
                      | (head11,args1) ->
                          let uu____12271 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12271 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12325 =
                                   let uu____12326 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12327 = args_to_string args1  in
                                   let uu____12328 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12329 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12326 uu____12327 uu____12328
                                     uu____12329
                                    in
                                 giveup env1 uu____12325 orig
                               else
                                 (let uu____12331 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12337 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12337 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12331
                                  then
                                    let uu____12338 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12338 with
                                    | USolved wl2 ->
                                        let uu____12340 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12340
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12344 =
                                       base_and_refinement env1 t1  in
                                     match uu____12344 with
                                     | (base1,refinement1) ->
                                         let uu____12369 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12369 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____12426 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____12426 with
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
                                                            (fun uu____12448 
                                                               ->
                                                               fun
                                                                 uu____12449 
                                                                 ->
                                                                 match 
                                                                   (uu____12448,
                                                                    uu____12449)
                                                                 with
                                                                 | ((a,uu____12467),
                                                                    (a',uu____12469))
                                                                    ->
                                                                    let uu____12478
                                                                    =
                                                                    let uu____12483
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12483
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
                                                                    uu____12478)
                                                            args1 args2
                                                           in
                                                        let formula =
                                                          let uu____12489 =
                                                            FStar_List.map
                                                              (fun p  ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____12489
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
                                               | uu____12495 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___147_12531 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___147_12531.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____12564 =
           match uu____12564 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____12606 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____12606 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____12702  ->
                      let uu____12703 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____12703);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____12771  ->
                                match uu____12771 with
                                | (x,imp) ->
                                    let uu____12782 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____12782, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____12795 = FStar_Syntax_Util.type_u ()  in
                        match uu____12795 with
                        | (t1,uu____12801) ->
                            let uu____12802 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____12802
                         in
                      let uu____12807 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____12807 with
                       | (t',tm_u1) ->
                           let uu____12820 = destruct_flex_t t'  in
                           (match uu____12820 with
                            | (uu____12857,u1,k1,uu____12860) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____12919 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____12919
                                   in
                                let sol =
                                  let uu____12923 =
                                    let uu____12932 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____12932)  in
                                  TERM uu____12923  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____13067  ->
                            let uu____13068 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____13069 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13068 uu____13069);
                       (let uu____13082 = pat_var_opt env pat_args hd1  in
                        match uu____13082 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____13102  ->
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
                                       (fun uu____13145  ->
                                          match uu____13145 with
                                          | (x,uu____13151) ->
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
                                 (fun uu____13166  ->
                                    let uu____13167 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____13180 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____13167
                                      uu____13180);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____13184 =
                                  let uu____13185 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____13185  in
                                if uu____13184
                                then
                                  (debug1
                                     (fun uu____13197  ->
                                        let uu____13198 =
                                          let uu____13201 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____13214 =
                                            let uu____13217 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____13218 =
                                              let uu____13221 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____13222 =
                                                let uu____13225 =
                                                  names_to_string fvs  in
                                                let uu____13226 =
                                                  let uu____13229 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____13229]  in
                                                uu____13225 :: uu____13226
                                                 in
                                              uu____13221 :: uu____13222  in
                                            uu____13217 :: uu____13218  in
                                          uu____13201 :: uu____13214  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____13198);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____13231 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____13234 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____13231 (formal ::
                                     pattern_vars) uu____13234 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____13241::uu____13242) ->
                      let uu____13273 =
                        let uu____13286 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____13286  in
                      (match uu____13273 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____13325 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____13332::uu____13333,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____13356 =
                 let uu____13369 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____13369  in
               (match uu____13356 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____13405  ->
                          let uu____13406 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____13407 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____13408 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____13409 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____13406 uu____13407 uu____13408 uu____13409);
                     (let uu____13410 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____13413 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____13410 [] uu____13413 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____13447 = lhs  in
           match uu____13447 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____13457 ->
                     let uu____13458 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____13458 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____13481 = p  in
           match uu____13481 with
           | (((u,k),xs,c),ps,(h,uu____13492,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13574 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____13574 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____13597 = h gs_xs  in
                      let uu____13598 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         in
                      FStar_Syntax_Util.abs xs1 uu____13597 uu____13598  in
                    ((let uu____13604 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13604
                      then
                        let uu____13605 =
                          let uu____13608 =
                            let uu____13609 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____13609
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____13614 =
                            let uu____13617 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____13618 =
                              let uu____13621 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____13622 =
                                let uu____13625 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____13626 =
                                  let uu____13629 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____13630 =
                                    let uu____13633 =
                                      let uu____13634 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____13634
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____13639 =
                                      let uu____13642 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____13642]  in
                                    uu____13633 :: uu____13639  in
                                  uu____13629 :: uu____13630  in
                                uu____13625 :: uu____13626  in
                              uu____13621 :: uu____13622  in
                            uu____13617 :: uu____13618  in
                          uu____13608 :: uu____13614  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____13605
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___111_13664 =
           match uu___111_13664 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____13696 = p  in
           match uu____13696 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13787 = FStar_List.nth ps i  in
               (match uu____13787 with
                | (pi,uu____13791) ->
                    let uu____13796 = FStar_List.nth xs i  in
                    (match uu____13796 with
                     | (xi,uu____13808) ->
                         let rec gs k =
                           let uu____13821 =
                             let uu____13834 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____13834  in
                           match uu____13821 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____13909)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____13922 = new_uvar r xs k_a  in
                                     (match uu____13922 with
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
                                          let uu____13944 = aux subst2 tl1
                                             in
                                          (match uu____13944 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____13971 =
                                                 let uu____13974 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____13974 :: gi_xs'  in
                                               let uu____13975 =
                                                 let uu____13978 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____13978 :: gi_ps'  in
                                               (uu____13971, uu____13975)))
                                  in
                               aux [] bs
                            in
                         let uu____13983 =
                           let uu____13984 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____13984
                            in
                         if uu____13983
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____13988 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____13988 with
                            | (g_xs,uu____14000) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____14011 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____14012 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_58  ->
                                         FStar_Pervasives_Native.Some _0_58)
                                     in
                                  FStar_Syntax_Util.abs xs uu____14011
                                    uu____14012
                                   in
                                let sub1 =
                                  let uu____14018 =
                                    let uu____14023 = p_scope orig  in
                                    let uu____14024 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____14027 =
                                      let uu____14030 =
                                        FStar_List.map
                                          (fun uu____14045  ->
                                             match uu____14045 with
                                             | (uu____14054,uu____14055,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____14030  in
                                    mk_problem uu____14023 orig uu____14024
                                      (p_rel orig) uu____14027
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_59  ->
                                       FStar_TypeChecker_Common.TProb _0_59)
                                    uu____14018
                                   in
                                ((let uu____14070 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14070
                                  then
                                    let uu____14071 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____14072 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____14071 uu____14072
                                  else ());
                                 (let wl2 =
                                    let uu____14075 =
                                      let uu____14078 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____14078
                                       in
                                    solve_prob orig uu____14075
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____14087 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_60  ->
                                       FStar_Pervasives_Native.Some _0_60)
                                    uu____14087)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____14118 = lhs  in
           match uu____14118 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____14154 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____14154 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____14187 =
                         let uu____14234 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____14234)  in
                       FStar_Pervasives_Native.Some uu____14187
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____14378 =
                            let uu____14385 =
                              let uu____14386 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____14386.FStar_Syntax_Syntax.n  in
                            (uu____14385, args)  in
                          match uu____14378 with
                          | (uu____14397,[]) ->
                              let uu____14400 =
                                let uu____14411 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____14411)  in
                              FStar_Pervasives_Native.Some uu____14400
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____14432,uu____14433) ->
                              let uu____14454 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14454 with
                               | (uv1,uv_args) ->
                                   let uu____14497 =
                                     let uu____14498 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14498.FStar_Syntax_Syntax.n  in
                                   (match uu____14497 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14508) ->
                                        let uu____14533 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14533 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14560  ->
                                                       let uu____14561 =
                                                         let uu____14562 =
                                                           let uu____14563 =
                                                             let uu____14568
                                                               =
                                                               let uu____14569
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14569
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14568
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14563
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14562
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14561))
                                                in
                                             let c1 =
                                               let uu____14579 =
                                                 let uu____14580 =
                                                   let uu____14585 =
                                                     let uu____14586 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14586
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14585
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14580
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14579
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14599 =
                                                 let uu____14602 =
                                                   let uu____14603 =
                                                     let uu____14606 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14606
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14603
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14602
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14599
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14625 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____14630,uu____14631) ->
                              let uu____14650 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14650 with
                               | (uv1,uv_args) ->
                                   let uu____14693 =
                                     let uu____14694 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14694.FStar_Syntax_Syntax.n  in
                                   (match uu____14693 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14704) ->
                                        let uu____14729 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14729 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14756  ->
                                                       let uu____14757 =
                                                         let uu____14758 =
                                                           let uu____14759 =
                                                             let uu____14764
                                                               =
                                                               let uu____14765
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14765
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14764
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14759
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14758
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14757))
                                                in
                                             let c1 =
                                               let uu____14775 =
                                                 let uu____14776 =
                                                   let uu____14781 =
                                                     let uu____14782 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14782
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14781
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14776
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14775
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14795 =
                                                 let uu____14798 =
                                                   let uu____14799 =
                                                     let uu____14802 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14802
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14799
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14798
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14795
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14821 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____14828) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____14869 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____14869
                                  (fun _0_61  ->
                                     FStar_Pervasives_Native.Some _0_61)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____14905 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____14905 with
                                   | (args1,rest) ->
                                       let uu____14934 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____14934 with
                                        | (xs2,c2) ->
                                            let uu____14947 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____14947
                                              (fun uu____14971  ->
                                                 match uu____14971 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____15011 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____15011 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15079 =
                                         let uu____15084 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____15084
                                          in
                                       FStar_All.pipe_right uu____15079
                                         (fun _0_62  ->
                                            FStar_Pervasives_Native.Some
                                              _0_62))
                          | uu____15099 ->
                              let uu____15106 =
                                let uu____15111 =
                                  let uu____15112 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____15113 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____15114 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____15112 uu____15113 uu____15114
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____15111)
                                 in
                              FStar_Errors.raise_error uu____15106
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____15121 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____15121
                          (fun uu____15176  ->
                             match uu____15176 with
                             | (xs1,c1) ->
                                 let uu____15225 =
                                   let uu____15266 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____15266)
                                    in
                                 FStar_Pervasives_Native.Some uu____15225))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____15387 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____15401 = project orig env wl1 i st  in
                      match uu____15401 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15415) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____15430 = imitate orig env wl1 st  in
                   match uu____15430 with
                   | Failed uu____15435 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____15466 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____15466 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____15489 = forced_lhs_pattern  in
                     (match uu____15489 with
                      | (lhs_t,uu____15491,uu____15492,uu____15493) ->
                          ((let uu____15495 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15495
                            then
                              let uu____15496 = lhs1  in
                              match uu____15496 with
                              | (t0,uu____15498,uu____15499,uu____15500) ->
                                  let uu____15501 = forced_lhs_pattern  in
                                  (match uu____15501 with
                                   | (t11,uu____15503,uu____15504,uu____15505)
                                       ->
                                       let uu____15506 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____15507 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____15506 uu____15507)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____15515 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____15515
                            then
                              ((let uu____15517 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15517
                                then
                                  let uu____15518 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____15519 = names_to_string rhs_vars
                                     in
                                  let uu____15520 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____15518 uu____15519 uu____15520
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____15524 =
                                  let uu____15525 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____15525 wl2  in
                                match uu____15524 with
                                | Failed uu____15526 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____15535 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15535
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____15548 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____15548 with
                 | (hd1,uu____15564) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____15585 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____15598 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____15599 -> true
                      | uu____15616 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____15620 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____15620
                          then true
                          else
                            ((let uu____15623 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____15623
                              then
                                let uu____15624 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____15624
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
                    let uu____15644 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____15644 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____15657 =
                             let uu____15658 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____15658
                              in
                           giveup_or_defer1 orig uu____15657
                         else
                           (let uu____15660 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____15660
                            then
                              let uu____15661 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____15661
                               then
                                 let uu____15662 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____15662
                               else
                                 ((let uu____15667 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____15667
                                   then
                                     let uu____15668 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____15669 = names_to_string fvs1
                                        in
                                     let uu____15670 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____15668 uu____15669 uu____15670
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
                                (let uu____15674 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____15674
                                 then
                                   ((let uu____15676 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____15676
                                     then
                                       let uu____15677 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____15678 = names_to_string fvs1
                                          in
                                       let uu____15679 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____15677 uu____15678 uu____15679
                                     else ());
                                    (let uu____15681 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____15681))
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
                      (let uu____15692 =
                         let uu____15693 = FStar_Syntax_Free.names t1  in
                         check_head uu____15693 t2  in
                       if uu____15692
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____15704 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15704
                           then
                             let uu____15705 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____15706 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____15705 uu____15706
                           else ());
                          (let uu____15714 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____15714))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____15791 uu____15792 r =
                match (uu____15791, uu____15792) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____15990 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____15990
                    then
                      let uu____15991 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____15991
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____16015 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____16015
                        then
                          let uu____16016 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____16017 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____16018 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____16019 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____16020 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16016 uu____16017 uu____16018 uu____16019
                            uu____16020
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____16080 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____16080 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____16094 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____16094 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____16148 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____16148
                                      in
                                   let uu____16151 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____16151 k3)
                            else
                              (let uu____16155 =
                                 let uu____16156 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____16157 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____16158 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____16156 uu____16157 uu____16158
                                  in
                               failwith uu____16155)
                           in
                        let uu____16159 =
                          let uu____16166 =
                            let uu____16179 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____16179  in
                          match uu____16166 with
                          | (bs,k1') ->
                              let uu____16204 =
                                let uu____16217 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____16217
                                 in
                              (match uu____16204 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____16245 =
                                       let uu____16250 = p_scope orig  in
                                       mk_problem uu____16250 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_63  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_63) uu____16245
                                      in
                                   let uu____16255 =
                                     let uu____16260 =
                                       let uu____16261 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____16261.FStar_Syntax_Syntax.n  in
                                     let uu____16264 =
                                       let uu____16265 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____16265.FStar_Syntax_Syntax.n  in
                                     (uu____16260, uu____16264)  in
                                   (match uu____16255 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____16274,uu____16275) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____16278,FStar_Syntax_Syntax.Tm_type
                                       uu____16279) -> (k2'_ys, [sub_prob])
                                    | uu____16282 ->
                                        let uu____16287 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____16287 with
                                         | (t,uu____16299) ->
                                             let uu____16300 =
                                               new_uvar r zs t  in
                                             (match uu____16300 with
                                              | (k_zs,uu____16312) ->
                                                  let kprob =
                                                    let uu____16314 =
                                                      let uu____16319 =
                                                        p_scope orig  in
                                                      mk_problem uu____16319
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_64  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_64) uu____16314
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____16159 with
                        | (k_u',sub_probs) ->
                            let uu____16332 =
                              let uu____16343 =
                                let uu____16344 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____16344
                                 in
                              let uu____16353 =
                                let uu____16356 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____16356  in
                              let uu____16359 =
                                let uu____16362 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____16362  in
                              (uu____16343, uu____16353, uu____16359)  in
                            (match uu____16332 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____16381 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____16381 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____16400 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____16400
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
                                            let uu____16404 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____16404 with
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
              let solve_one_pat uu____16457 uu____16458 =
                match (uu____16457, uu____16458) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____16576 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____16576
                      then
                        let uu____16577 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____16578 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____16577 uu____16578
                      else ());
                     (let uu____16580 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____16580
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____16599  ->
                               fun uu____16600  ->
                                 match (uu____16599, uu____16600) with
                                 | ((a,uu____16618),(t21,uu____16620)) ->
                                     let uu____16629 =
                                       let uu____16634 = p_scope orig  in
                                       let uu____16635 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____16634 orig
                                         uu____16635
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____16629
                                       (fun _0_65  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_65)) xs args2
                           in
                        let guard =
                          let uu____16641 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____16641  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____16656 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____16656 with
                         | (occurs_ok,uu____16664) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____16672 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____16672
                             then
                               let sol =
                                 let uu____16674 =
                                   let uu____16683 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____16683)  in
                                 TERM uu____16674  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____16690 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____16690
                                then
                                  let uu____16691 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____16691 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____16715,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____16741 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____16741
                                        then
                                          let uu____16742 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____16742
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____16749 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____16751 = lhs  in
              match uu____16751 with
              | (t1,u1,k1,args1) ->
                  let uu____16756 = rhs  in
                  (match uu____16756 with
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
                        | uu____16796 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____16806 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____16806 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____16824) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____16831 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____16831
                                     then
                                       let uu____16832 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____16832
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____16839 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____16842 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____16842
          then
            let uu____16843 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____16843
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____16847 = FStar_Util.physical_equality t1 t2  in
             if uu____16847
             then
               let uu____16848 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____16848
             else
               ((let uu____16851 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____16851
                 then
                   let uu____16852 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____16853 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____16854 = FStar_Syntax_Print.tag_of_term t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____16852
                     uu____16853 uu____16854
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let not_quote t =
                   let uu____16861 =
                     let uu____16862 = FStar_Syntax_Subst.compress t  in
                     uu____16862.FStar_Syntax_Syntax.n  in
                   match uu____16861 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____16865,FStar_Syntax_Syntax.Meta_quoted
                        uu____16866)
                       -> false
                   | uu____16877 -> true  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____16878,uu____16879)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____16904,FStar_Syntax_Syntax.Tm_delayed uu____16905)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____16930,uu____16931)
                     ->
                     let uu____16958 =
                       let uu___148_16959 = problem  in
                       let uu____16960 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_16959.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____16960;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_16959.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___148_16959.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___148_16959.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_16959.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_16959.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_16959.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_16959.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_16959.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____16958 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____16961,uu____16962) when
                     not_quote t1 ->
                     let uu____16969 =
                       let uu___149_16970 = problem  in
                       let uu____16971 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___149_16970.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____16971;
                         FStar_TypeChecker_Common.relation =
                           (uu___149_16970.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___149_16970.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___149_16970.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___149_16970.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___149_16970.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___149_16970.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___149_16970.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___149_16970.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____16969 wl
                 | (uu____16972,FStar_Syntax_Syntax.Tm_ascribed uu____16973)
                     ->
                     let uu____17000 =
                       let uu___150_17001 = problem  in
                       let uu____17002 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_17001.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___150_17001.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___150_17001.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17002;
                         FStar_TypeChecker_Common.element =
                           (uu___150_17001.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_17001.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_17001.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_17001.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_17001.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_17001.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17000 wl
                 | (uu____17003,FStar_Syntax_Syntax.Tm_meta uu____17004) when
                     not_quote t2 ->
                     let uu____17011 =
                       let uu___151_17012 = problem  in
                       let uu____17013 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_17012.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___151_17012.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___151_17012.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17013;
                         FStar_TypeChecker_Common.element =
                           (uu___151_17012.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_17012.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_17012.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_17012.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_17012.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_17012.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17011 wl
                 | (FStar_Syntax_Syntax.Tm_meta
                    (uu____17014,FStar_Syntax_Syntax.Meta_quoted
                     (t11,uu____17016)),FStar_Syntax_Syntax.Tm_meta
                    (uu____17017,FStar_Syntax_Syntax.Meta_quoted
                     (t21,uu____17019))) ->
                     let uu____17036 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____17036
                 | (FStar_Syntax_Syntax.Tm_bvar uu____17037,uu____17038) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____17039,FStar_Syntax_Syntax.Tm_bvar uu____17040) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___112_17095 =
                       match uu___112_17095 with
                       | [] -> c
                       | bs ->
                           let uu____17117 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____17117
                        in
                     let uu____17126 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____17126 with
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
                                     let uu____17268 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____17268
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____17270 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_66  ->
                                        FStar_TypeChecker_Common.CProb _0_66)
                                     uu____17270))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___113_17346 =
                       match uu___113_17346 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____17380 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____17380 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____17516 =
                                     let uu____17521 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____17522 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____17521
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____17522
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_67  ->
                                        FStar_TypeChecker_Common.TProb _0_67)
                                     uu____17516))
                 | (FStar_Syntax_Syntax.Tm_abs uu____17527,uu____17528) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17553 -> true
                       | uu____17570 -> false  in
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
                         (let uu____17617 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_17625 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_17625.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_17625.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_17625.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_17625.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_17625.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_17625.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_17625.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_17625.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_17625.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_17625.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_17625.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_17625.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_17625.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_17625.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_17625.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_17625.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_17625.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_17625.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_17625.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_17625.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_17625.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_17625.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_17625.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_17625.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_17625.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_17625.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___152_17625.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_17625.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_17625.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_17625.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_17625.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_17625.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_17625.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17617 with
                          | (uu____17628,ty,uu____17630) ->
                              let uu____17631 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17631)
                        in
                     let uu____17632 =
                       let uu____17649 = maybe_eta t1  in
                       let uu____17656 = maybe_eta t2  in
                       (uu____17649, uu____17656)  in
                     (match uu____17632 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_17698 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_17698.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_17698.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_17698.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_17698.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_17698.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_17698.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_17698.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_17698.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____17721 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17721
                          then
                            let uu____17722 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17722 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_17737 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_17737.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_17737.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_17737.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_17737.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_17737.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_17737.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_17737.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_17737.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____17761 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17761
                          then
                            let uu____17762 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17762 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_17777 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_17777.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_17777.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_17777.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_17777.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_17777.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_17777.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_17777.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_17777.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____17781 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____17798,FStar_Syntax_Syntax.Tm_abs uu____17799) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17824 -> true
                       | uu____17841 -> false  in
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
                         (let uu____17888 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_17896 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_17896.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_17896.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_17896.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_17896.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_17896.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_17896.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_17896.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_17896.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_17896.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_17896.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_17896.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_17896.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_17896.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_17896.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_17896.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_17896.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_17896.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_17896.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_17896.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_17896.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_17896.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_17896.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_17896.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_17896.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_17896.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_17896.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___152_17896.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_17896.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_17896.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_17896.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_17896.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_17896.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_17896.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17888 with
                          | (uu____17899,ty,uu____17901) ->
                              let uu____17902 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17902)
                        in
                     let uu____17903 =
                       let uu____17920 = maybe_eta t1  in
                       let uu____17927 = maybe_eta t2  in
                       (uu____17920, uu____17927)  in
                     (match uu____17903 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_17969 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_17969.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_17969.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_17969.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_17969.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_17969.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_17969.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_17969.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_17969.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____17992 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17992
                          then
                            let uu____17993 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17993 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18008 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18008.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18008.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18008.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18008.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18008.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18008.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18008.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18008.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18032 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18032
                          then
                            let uu____18033 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18033 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18048 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18048.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18048.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18048.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18048.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18048.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18048.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18048.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18048.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18052 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____18084 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____18084) &&
                          (let uu____18096 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____18096))
                         &&
                         (let uu____18111 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____18111 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___114_18121 =
                                match uu___114_18121 with
                                | FStar_Syntax_Syntax.Delta_constant  -> true
                                | FStar_Syntax_Syntax.Delta_defined_at_level
                                    uu____18122 -> true
                                | uu____18123 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____18124 -> false)
                        in
                     let uu____18125 = as_refinement should_delta env wl t1
                        in
                     (match uu____18125 with
                      | (x11,phi1) ->
                          let uu____18132 =
                            as_refinement should_delta env wl t2  in
                          (match uu____18132 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____18140 =
                                   let uu____18145 = p_scope orig  in
                                   mk_problem uu____18145 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____18140
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
                                 let uu____18179 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____18179
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____18183 =
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
                                   let uu____18189 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____18189 impl
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
                                   let uu____18198 =
                                     let uu____18203 =
                                       let uu____18204 = p_scope orig  in
                                       let uu____18211 =
                                         let uu____18218 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____18218]  in
                                       FStar_List.append uu____18204
                                         uu____18211
                                        in
                                     mk_problem uu____18203 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_69  ->
                                        FStar_TypeChecker_Common.TProb _0_69)
                                     uu____18198
                                    in
                                 let uu____18227 =
                                   solve env1
                                     (let uu___155_18229 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___155_18229.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___155_18229.smt_ok);
                                        tcenv = (uu___155_18229.tcenv)
                                      })
                                    in
                                 (match uu____18227 with
                                  | Failed uu____18236 -> fallback ()
                                  | Success uu____18241 ->
                                      let guard =
                                        let uu____18245 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____18250 =
                                          let uu____18251 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____18251
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____18245
                                          uu____18250
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___156_18260 = wl1  in
                                        {
                                          attempting =
                                            (uu___156_18260.attempting);
                                          wl_deferred =
                                            (uu___156_18260.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___156_18260.defer_ok);
                                          smt_ok = (uu___156_18260.smt_ok);
                                          tcenv = (uu___156_18260.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18262,FStar_Syntax_Syntax.Tm_uvar uu____18263) ->
                     let uu____18296 = destruct_flex_t t1  in
                     let uu____18297 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18296 uu____18297
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18298;
                       FStar_Syntax_Syntax.pos = uu____18299;
                       FStar_Syntax_Syntax.vars = uu____18300;_},uu____18301),FStar_Syntax_Syntax.Tm_uvar
                    uu____18302) ->
                     let uu____18355 = destruct_flex_t t1  in
                     let uu____18356 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18355 uu____18356
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18357,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18358;
                       FStar_Syntax_Syntax.pos = uu____18359;
                       FStar_Syntax_Syntax.vars = uu____18360;_},uu____18361))
                     ->
                     let uu____18414 = destruct_flex_t t1  in
                     let uu____18415 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18414 uu____18415
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18416;
                       FStar_Syntax_Syntax.pos = uu____18417;
                       FStar_Syntax_Syntax.vars = uu____18418;_},uu____18419),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18420;
                       FStar_Syntax_Syntax.pos = uu____18421;
                       FStar_Syntax_Syntax.vars = uu____18422;_},uu____18423))
                     ->
                     let uu____18496 = destruct_flex_t t1  in
                     let uu____18497 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18496 uu____18497
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18498,uu____18499) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18516 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18516 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18523;
                       FStar_Syntax_Syntax.pos = uu____18524;
                       FStar_Syntax_Syntax.vars = uu____18525;_},uu____18526),uu____18527)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18564 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18564 t2 wl
                 | (uu____18571,FStar_Syntax_Syntax.Tm_uvar uu____18572) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____18589,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18590;
                       FStar_Syntax_Syntax.pos = uu____18591;
                       FStar_Syntax_Syntax.vars = uu____18592;_},uu____18593))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18630,FStar_Syntax_Syntax.Tm_type uu____18631) ->
                     solve_t' env
                       (let uu___157_18649 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18649.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18649.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18649.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18649.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18649.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18649.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18649.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18649.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18649.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18650;
                       FStar_Syntax_Syntax.pos = uu____18651;
                       FStar_Syntax_Syntax.vars = uu____18652;_},uu____18653),FStar_Syntax_Syntax.Tm_type
                    uu____18654) ->
                     solve_t' env
                       (let uu___157_18692 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18692.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18692.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18692.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18692.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18692.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18692.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18692.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18692.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18692.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18693,FStar_Syntax_Syntax.Tm_arrow uu____18694) ->
                     solve_t' env
                       (let uu___157_18724 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18724.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18724.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18724.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18724.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18724.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18724.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18724.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18724.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18724.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18725;
                       FStar_Syntax_Syntax.pos = uu____18726;
                       FStar_Syntax_Syntax.vars = uu____18727;_},uu____18728),FStar_Syntax_Syntax.Tm_arrow
                    uu____18729) ->
                     solve_t' env
                       (let uu___157_18779 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18779.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18779.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18779.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18779.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18779.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18779.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18779.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18779.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18779.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18780,uu____18781) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____18800 =
                          let uu____18801 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____18801
                           in
                        if uu____18800
                        then
                          let uu____18802 =
                            FStar_All.pipe_left
                              (fun _0_70  ->
                                 FStar_TypeChecker_Common.TProb _0_70)
                              (let uu___158_18808 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_18808.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_18808.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_18808.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_18808.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_18808.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_18808.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_18808.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_18808.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_18808.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____18809 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____18802 uu____18809 t2
                            wl
                        else
                          (let uu____18817 = base_and_refinement env t2  in
                           match uu____18817 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18846 =
                                      FStar_All.pipe_left
                                        (fun _0_71  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_71)
                                        (let uu___159_18852 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_18852.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_18852.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_18852.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_18852.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_18852.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_18852.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_18852.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_18852.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_18852.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____18853 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____18846
                                      uu____18853 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_18867 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_18867.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_18867.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____18870 =
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
                                             _0_72) uu____18870
                                       in
                                    let guard =
                                      let uu____18882 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18882
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
                         uu____18890;
                       FStar_Syntax_Syntax.pos = uu____18891;
                       FStar_Syntax_Syntax.vars = uu____18892;_},uu____18893),uu____18894)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____18933 =
                          let uu____18934 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____18934
                           in
                        if uu____18933
                        then
                          let uu____18935 =
                            FStar_All.pipe_left
                              (fun _0_73  ->
                                 FStar_TypeChecker_Common.TProb _0_73)
                              (let uu___158_18941 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_18941.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_18941.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_18941.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_18941.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_18941.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_18941.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_18941.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_18941.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_18941.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____18942 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____18935 uu____18942 t2
                            wl
                        else
                          (let uu____18950 = base_and_refinement env t2  in
                           match uu____18950 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18979 =
                                      FStar_All.pipe_left
                                        (fun _0_74  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_74)
                                        (let uu___159_18985 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_18985.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_18985.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_18985.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_18985.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_18985.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_18985.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_18985.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_18985.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_18985.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____18986 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____18979
                                      uu____18986 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_19000 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_19000.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_19000.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19003 =
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
                                             _0_75) uu____19003
                                       in
                                    let guard =
                                      let uu____19015 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19015
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____19023,FStar_Syntax_Syntax.Tm_uvar uu____19024) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19042 = base_and_refinement env t1  in
                        match uu____19042 with
                        | (t_base,uu____19054) ->
                            solve_t env
                              (let uu___161_19068 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19068.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19068.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19068.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19068.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19068.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19068.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19068.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19068.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____19069,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19070;
                       FStar_Syntax_Syntax.pos = uu____19071;
                       FStar_Syntax_Syntax.vars = uu____19072;_},uu____19073))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19111 = base_and_refinement env t1  in
                        match uu____19111 with
                        | (t_base,uu____19123) ->
                            solve_t env
                              (let uu___161_19137 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19137.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19137.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19137.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19137.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19137.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19137.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19137.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19137.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____19138,uu____19139) ->
                     let t21 =
                       let uu____19149 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____19149  in
                     solve_t env
                       (let uu___162_19173 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___162_19173.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___162_19173.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___162_19173.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___162_19173.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___162_19173.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___162_19173.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___162_19173.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___162_19173.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___162_19173.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19174,FStar_Syntax_Syntax.Tm_refine uu____19175) ->
                     let t11 =
                       let uu____19185 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____19185  in
                     solve_t env
                       (let uu___163_19209 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___163_19209.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___163_19209.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___163_19209.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___163_19209.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___163_19209.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___163_19209.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___163_19209.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___163_19209.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___163_19209.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match uu____19212,uu____19213) ->
                     let head1 =
                       let uu____19239 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19239
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19283 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19283
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19325 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19325
                       then
                         let uu____19326 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19327 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19328 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19326 uu____19327 uu____19328
                       else ());
                      (let uu____19330 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19330
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19345 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19345
                          then
                            let guard =
                              let uu____19357 =
                                let uu____19358 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19358 = FStar_Syntax_Util.Equal  in
                              if uu____19357
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19362 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_76  ->
                                      FStar_Pervasives_Native.Some _0_76)
                                   uu____19362)
                               in
                            let uu____19365 = solve_prob orig guard [] wl  in
                            solve env uu____19365
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____19368,uu____19369) ->
                     let head1 =
                       let uu____19379 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19379
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19423 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19423
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19465 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19465
                       then
                         let uu____19466 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19467 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19468 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19466 uu____19467 uu____19468
                       else ());
                      (let uu____19470 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19470
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19485 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19485
                          then
                            let guard =
                              let uu____19497 =
                                let uu____19498 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19498 = FStar_Syntax_Util.Equal  in
                              if uu____19497
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19502 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_77  ->
                                      FStar_Pervasives_Native.Some _0_77)
                                   uu____19502)
                               in
                            let uu____19505 = solve_prob orig guard [] wl  in
                            solve env uu____19505
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____19508,uu____19509) ->
                     let head1 =
                       let uu____19513 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19513
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19557 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19557
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19599 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19599
                       then
                         let uu____19600 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19601 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19602 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19600 uu____19601 uu____19602
                       else ());
                      (let uu____19604 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19604
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19619 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19619
                          then
                            let guard =
                              let uu____19631 =
                                let uu____19632 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19632 = FStar_Syntax_Util.Equal  in
                              if uu____19631
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19636 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_78  ->
                                      FStar_Pervasives_Native.Some _0_78)
                                   uu____19636)
                               in
                            let uu____19639 = solve_prob orig guard [] wl  in
                            solve env uu____19639
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____19642,uu____19643)
                     ->
                     let head1 =
                       let uu____19647 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19647
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19691 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19691
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19733 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19733
                       then
                         let uu____19734 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19735 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19736 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19734 uu____19735 uu____19736
                       else ());
                      (let uu____19738 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19738
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19753 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19753
                          then
                            let guard =
                              let uu____19765 =
                                let uu____19766 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19766 = FStar_Syntax_Util.Equal  in
                              if uu____19765
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19770 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_79  ->
                                      FStar_Pervasives_Native.Some _0_79)
                                   uu____19770)
                               in
                            let uu____19773 = solve_prob orig guard [] wl  in
                            solve env uu____19773
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____19776,uu____19777) ->
                     let head1 =
                       let uu____19781 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19781
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19825 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19825
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19867 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19867
                       then
                         let uu____19868 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19869 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19870 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19868 uu____19869 uu____19870
                       else ());
                      (let uu____19872 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19872
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19887 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19887
                          then
                            let guard =
                              let uu____19899 =
                                let uu____19900 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19900 = FStar_Syntax_Util.Equal  in
                              if uu____19899
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19904 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_80  ->
                                      FStar_Pervasives_Native.Some _0_80)
                                   uu____19904)
                               in
                            let uu____19907 = solve_prob orig guard [] wl  in
                            solve env uu____19907
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____19910,uu____19911) ->
                     let head1 =
                       let uu____19929 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19929
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19973 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19973
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20015 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20015
                       then
                         let uu____20016 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20017 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20018 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20016 uu____20017 uu____20018
                       else ());
                      (let uu____20020 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20020
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20035 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20035
                          then
                            let guard =
                              let uu____20047 =
                                let uu____20048 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20048 = FStar_Syntax_Util.Equal  in
                              if uu____20047
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20052 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_81  ->
                                      FStar_Pervasives_Native.Some _0_81)
                                   uu____20052)
                               in
                            let uu____20055 = solve_prob orig guard [] wl  in
                            solve env uu____20055
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20058,FStar_Syntax_Syntax.Tm_match uu____20059) ->
                     let head1 =
                       let uu____20085 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20085
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20129 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20129
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20171 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20171
                       then
                         let uu____20172 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20173 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20174 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20172 uu____20173 uu____20174
                       else ());
                      (let uu____20176 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20176
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20191 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20191
                          then
                            let guard =
                              let uu____20203 =
                                let uu____20204 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20204 = FStar_Syntax_Util.Equal  in
                              if uu____20203
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20208 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_82  ->
                                      FStar_Pervasives_Native.Some _0_82)
                                   uu____20208)
                               in
                            let uu____20211 = solve_prob orig guard [] wl  in
                            solve env uu____20211
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20214,FStar_Syntax_Syntax.Tm_uinst uu____20215) ->
                     let head1 =
                       let uu____20225 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20225
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20269 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20269
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20311 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20311
                       then
                         let uu____20312 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20313 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20314 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20312 uu____20313 uu____20314
                       else ());
                      (let uu____20316 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20316
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20331 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20331
                          then
                            let guard =
                              let uu____20343 =
                                let uu____20344 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20344 = FStar_Syntax_Util.Equal  in
                              if uu____20343
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20348 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_83  ->
                                      FStar_Pervasives_Native.Some _0_83)
                                   uu____20348)
                               in
                            let uu____20351 = solve_prob orig guard [] wl  in
                            solve env uu____20351
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20354,FStar_Syntax_Syntax.Tm_name uu____20355) ->
                     let head1 =
                       let uu____20359 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20359
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20403 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20403
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20445 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20445
                       then
                         let uu____20446 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20447 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20448 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20446 uu____20447 uu____20448
                       else ());
                      (let uu____20450 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20450
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20465 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20465
                          then
                            let guard =
                              let uu____20477 =
                                let uu____20478 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20478 = FStar_Syntax_Util.Equal  in
                              if uu____20477
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20482 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_84  ->
                                      FStar_Pervasives_Native.Some _0_84)
                                   uu____20482)
                               in
                            let uu____20485 = solve_prob orig guard [] wl  in
                            solve env uu____20485
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20488,FStar_Syntax_Syntax.Tm_constant uu____20489)
                     ->
                     let head1 =
                       let uu____20493 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20493
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20537 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20537
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20579 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20579
                       then
                         let uu____20580 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20581 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20582 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20580 uu____20581 uu____20582
                       else ());
                      (let uu____20584 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20584
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20599 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20599
                          then
                            let guard =
                              let uu____20611 =
                                let uu____20612 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20612 = FStar_Syntax_Util.Equal  in
                              if uu____20611
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20616 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_85  ->
                                      FStar_Pervasives_Native.Some _0_85)
                                   uu____20616)
                               in
                            let uu____20619 = solve_prob orig guard [] wl  in
                            solve env uu____20619
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20622,FStar_Syntax_Syntax.Tm_fvar uu____20623) ->
                     let head1 =
                       let uu____20627 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20627
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20671 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20671
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20713 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20713
                       then
                         let uu____20714 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20715 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20716 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20714 uu____20715 uu____20716
                       else ());
                      (let uu____20718 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20718
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20733 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20733
                          then
                            let guard =
                              let uu____20745 =
                                let uu____20746 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20746 = FStar_Syntax_Util.Equal  in
                              if uu____20745
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20750 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_86  ->
                                      FStar_Pervasives_Native.Some _0_86)
                                   uu____20750)
                               in
                            let uu____20753 = solve_prob orig guard [] wl  in
                            solve env uu____20753
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20756,FStar_Syntax_Syntax.Tm_app uu____20757) ->
                     let head1 =
                       let uu____20775 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20775
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20819 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20819
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20861 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20861
                       then
                         let uu____20862 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20863 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20864 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20862 uu____20863 uu____20864
                       else ());
                      (let uu____20866 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20866
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20881 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20881
                          then
                            let guard =
                              let uu____20893 =
                                let uu____20894 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20894 = FStar_Syntax_Util.Equal  in
                              if uu____20893
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20898 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_87  ->
                                      FStar_Pervasives_Native.Some _0_87)
                                   uu____20898)
                               in
                            let uu____20901 = solve_prob orig guard [] wl  in
                            solve env uu____20901
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____20904,FStar_Syntax_Syntax.Tm_let uu____20905) ->
                     let uu____20930 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____20930
                     then
                       let uu____20931 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____20931
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____20933,uu____20934) ->
                     let uu____20947 =
                       let uu____20952 =
                         let uu____20953 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20954 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____20955 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____20956 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____20953 uu____20954 uu____20955 uu____20956
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____20952)
                        in
                     FStar_Errors.raise_error uu____20947
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____20957,FStar_Syntax_Syntax.Tm_let uu____20958) ->
                     let uu____20971 =
                       let uu____20976 =
                         let uu____20977 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20978 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____20979 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____20980 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____20977 uu____20978 uu____20979 uu____20980
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____20976)
                        in
                     FStar_Errors.raise_error uu____20971
                       t1.FStar_Syntax_Syntax.pos
                 | uu____20981 -> giveup env "head tag mismatch" orig)))))

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
          let uu____21009 = p_scope orig  in
          mk_problem uu____21009 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____21018 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21018
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____21020 =
               let uu____21021 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21022 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21021 uu____21022
                in
             giveup env uu____21020 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____21042  ->
                    fun uu____21043  ->
                      match (uu____21042, uu____21043) with
                      | ((a1,uu____21061),(a2,uu____21063)) ->
                          let uu____21072 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21072)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____21082 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____21082  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21106 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21113)::[] -> wp1
              | uu____21130 ->
                  let uu____21139 =
                    let uu____21140 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21140
                     in
                  failwith uu____21139
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21148 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21148]
              | x -> x  in
            let uu____21150 =
              let uu____21159 =
                let uu____21160 =
                  let uu____21161 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21161 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21160  in
              [uu____21159]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21150;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21162 = lift_c1 ()  in solve_eq uu____21162 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___115_21168  ->
                       match uu___115_21168 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21169 -> false))
                in
             let uu____21170 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21204)::uu____21205,(wp2,uu____21207)::uu____21208)
                   -> (wp1, wp2)
               | uu____21265 ->
                   let uu____21286 =
                     let uu____21291 =
                       let uu____21292 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21293 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21292 uu____21293
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21291)
                      in
                   FStar_Errors.raise_error uu____21286
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21170 with
             | (wpc1,wpc2) ->
                 let uu____21312 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21312
                 then
                   let uu____21315 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21315 wl
                 else
                   (let uu____21319 =
                      let uu____21326 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21326  in
                    match uu____21319 with
                    | (c2_decl,qualifiers) ->
                        let uu____21347 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21347
                        then
                          let c1_repr =
                            let uu____21351 =
                              let uu____21352 =
                                let uu____21353 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21353  in
                              let uu____21354 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21352 uu____21354
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21351
                             in
                          let c2_repr =
                            let uu____21356 =
                              let uu____21357 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21358 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21357 uu____21358
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21356
                             in
                          let prob =
                            let uu____21360 =
                              let uu____21365 =
                                let uu____21366 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21367 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21366
                                  uu____21367
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21365
                               in
                            FStar_TypeChecker_Common.TProb uu____21360  in
                          let wl1 =
                            let uu____21369 =
                              let uu____21372 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21372  in
                            solve_prob orig uu____21369 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21381 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21381
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21384 =
                                     let uu____21387 =
                                       let uu____21388 =
                                         let uu____21403 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21404 =
                                           let uu____21407 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21408 =
                                             let uu____21411 =
                                               let uu____21412 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21412
                                                in
                                             [uu____21411]  in
                                           uu____21407 :: uu____21408  in
                                         (uu____21403, uu____21404)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21388
                                        in
                                     FStar_Syntax_Syntax.mk uu____21387  in
                                   uu____21384 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21421 =
                                    let uu____21424 =
                                      let uu____21425 =
                                        let uu____21440 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21441 =
                                          let uu____21444 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21445 =
                                            let uu____21448 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21449 =
                                              let uu____21452 =
                                                let uu____21453 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21453
                                                 in
                                              [uu____21452]  in
                                            uu____21448 :: uu____21449  in
                                          uu____21444 :: uu____21445  in
                                        (uu____21440, uu____21441)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21425
                                       in
                                    FStar_Syntax_Syntax.mk uu____21424  in
                                  uu____21421 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21460 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21460
                              in
                           let wl1 =
                             let uu____21470 =
                               let uu____21473 =
                                 let uu____21476 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21476 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21473
                                in
                             solve_prob orig uu____21470 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21489 = FStar_Util.physical_equality c1 c2  in
        if uu____21489
        then
          let uu____21490 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21490
        else
          ((let uu____21493 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21493
            then
              let uu____21494 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21495 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21494
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21495
            else ());
           (let uu____21497 =
              let uu____21502 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21503 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21502, uu____21503)  in
            match uu____21497 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21507),FStar_Syntax_Syntax.Total
                    (t2,uu____21509)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21526 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21526 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21529,FStar_Syntax_Syntax.Total uu____21530) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21548),FStar_Syntax_Syntax.Total
                    (t2,uu____21550)) ->
                     let uu____21567 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21567 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21571),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21573)) ->
                     let uu____21590 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21590 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21594),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21596)) ->
                     let uu____21613 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21613 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21616,FStar_Syntax_Syntax.Comp uu____21617) ->
                     let uu____21626 =
                       let uu___164_21631 = problem  in
                       let uu____21636 =
                         let uu____21637 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21637
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21631.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21636;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21631.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21631.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21631.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21631.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21631.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21631.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21631.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21631.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21626 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21638,FStar_Syntax_Syntax.Comp uu____21639) ->
                     let uu____21648 =
                       let uu___164_21653 = problem  in
                       let uu____21658 =
                         let uu____21659 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21659
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21653.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21658;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21653.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21653.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21653.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21653.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21653.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21653.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21653.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21653.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21648 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21660,FStar_Syntax_Syntax.GTotal uu____21661) ->
                     let uu____21670 =
                       let uu___165_21675 = problem  in
                       let uu____21680 =
                         let uu____21681 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21681
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21675.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21675.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21675.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21680;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21675.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21675.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21675.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21675.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21675.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21675.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21670 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21682,FStar_Syntax_Syntax.Total uu____21683) ->
                     let uu____21692 =
                       let uu___165_21697 = problem  in
                       let uu____21702 =
                         let uu____21703 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21703
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21697.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21697.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21697.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21702;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21697.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21697.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21697.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21697.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21697.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21697.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21692 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21704,FStar_Syntax_Syntax.Comp uu____21705) ->
                     let uu____21706 =
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
                     if uu____21706
                     then
                       let uu____21707 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21707 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21713 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21723 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21724 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21723, uu____21724))
                             in
                          match uu____21713 with
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
                           (let uu____21731 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21731
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21733 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21733 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21736 =
                                  let uu____21737 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21738 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21737 uu____21738
                                   in
                                giveup env uu____21736 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21743 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21781  ->
              match uu____21781 with
              | (uu____21794,uu____21795,u,uu____21797,uu____21798,uu____21799)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21743 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21830 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21830 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21848 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21876  ->
                match uu____21876 with
                | (u1,u2) ->
                    let uu____21883 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21884 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21883 uu____21884))
         in
      FStar_All.pipe_right uu____21848 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21901,[])) -> "{}"
      | uu____21926 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21943 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21943
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21946 =
              FStar_List.map
                (fun uu____21956  ->
                   match uu____21956 with
                   | (uu____21961,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21946 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21966 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21966 imps
  
let new_t_problem :
  'Auu____21974 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21974 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21974)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____22008 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____22008
                then
                  let uu____22009 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____22010 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22009
                    (rel_to_string rel) uu____22010
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
            let uu____22034 =
              let uu____22037 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____22037
               in
            FStar_Syntax_Syntax.new_bv uu____22034 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____22046 =
              let uu____22049 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____22049
               in
            let uu____22052 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____22046 uu____22052  in
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
          let uu____22082 = FStar_Options.eager_inference ()  in
          if uu____22082
          then
            let uu___166_22083 = probs  in
            {
              attempting = (uu___166_22083.attempting);
              wl_deferred = (uu___166_22083.wl_deferred);
              ctr = (uu___166_22083.ctr);
              defer_ok = false;
              smt_ok = (uu___166_22083.smt_ok);
              tcenv = (uu___166_22083.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22094 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22094
              then
                let uu____22095 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22095
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
          ((let uu____22109 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22109
            then
              let uu____22110 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22110
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22114 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22114
             then
               let uu____22115 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22115
             else ());
            (let f2 =
               let uu____22118 =
                 let uu____22119 = FStar_Syntax_Util.unmeta f1  in
                 uu____22119.FStar_Syntax_Syntax.n  in
               match uu____22118 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22123 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___167_22124 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_22124.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_22124.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_22124.FStar_TypeChecker_Env.implicits)
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
            let uu____22143 =
              let uu____22144 =
                let uu____22145 =
                  let uu____22146 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22146
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22145;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22144  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____22143
  
let with_guard_no_simp :
  'Auu____22173 .
    'Auu____22173 ->
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
            let uu____22193 =
              let uu____22194 =
                let uu____22195 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22195
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22194;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22193
  
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
          (let uu____22233 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22233
           then
             let uu____22234 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22235 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22234
               uu____22235
           else ());
          (let prob =
             let uu____22238 =
               let uu____22243 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22243
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22238
              in
           let g =
             let uu____22251 =
               let uu____22254 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22254
                 (fun uu____22256  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22251  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22274 = try_teq true env t1 t2  in
        match uu____22274 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22278 = FStar_TypeChecker_Env.get_range env  in
              let uu____22279 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22278 uu____22279);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22286 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22286
              then
                let uu____22287 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22288 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22289 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22287
                  uu____22288 uu____22289
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
          let uu____22303 = FStar_TypeChecker_Env.get_range env  in
          let uu____22304 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22303 uu____22304
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22321 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22321
         then
           let uu____22322 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22323 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22322
             uu____22323
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22328 =
             let uu____22333 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22333 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22328
            in
         let uu____22338 =
           let uu____22341 = singleton env prob  in
           solve_and_commit env uu____22341
             (fun uu____22343  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22338)
  
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
      fun uu____22372  ->
        match uu____22372 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22411 =
                 let uu____22416 =
                   let uu____22417 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22418 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22417 uu____22418
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22416)  in
               let uu____22419 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22411 uu____22419)
               in
            let equiv1 v1 v' =
              let uu____22427 =
                let uu____22432 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22433 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22432, uu____22433)  in
              match uu____22427 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22452 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22482 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22482 with
                      | FStar_Syntax_Syntax.U_unif uu____22489 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22518  ->
                                    match uu____22518 with
                                    | (u,v') ->
                                        let uu____22527 = equiv1 v1 v'  in
                                        if uu____22527
                                        then
                                          let uu____22530 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22530 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22546 -> []))
               in
            let uu____22551 =
              let wl =
                let uu___168_22555 = empty_worklist env  in
                {
                  attempting = (uu___168_22555.attempting);
                  wl_deferred = (uu___168_22555.wl_deferred);
                  ctr = (uu___168_22555.ctr);
                  defer_ok = false;
                  smt_ok = (uu___168_22555.smt_ok);
                  tcenv = (uu___168_22555.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22573  ->
                      match uu____22573 with
                      | (lb,v1) ->
                          let uu____22580 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22580 with
                           | USolved wl1 -> ()
                           | uu____22582 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22590 =
              match uu____22590 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22599) -> true
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
                      uu____22622,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22624,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22635) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22642,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22650 -> false)
               in
            let uu____22655 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22670  ->
                      match uu____22670 with
                      | (u,v1) ->
                          let uu____22677 = check_ineq (u, v1)  in
                          if uu____22677
                          then true
                          else
                            ((let uu____22680 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22680
                              then
                                let uu____22681 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22682 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22681
                                  uu____22682
                              else ());
                             false)))
               in
            if uu____22655
            then ()
            else
              ((let uu____22686 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22686
                then
                  ((let uu____22688 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22688);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22698 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22698))
                else ());
               (let uu____22708 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22708))
  
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
      let fail1 uu____22756 =
        match uu____22756 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22770 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22770
       then
         let uu____22771 = wl_to_string wl  in
         let uu____22772 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22771 uu____22772
       else ());
      (let g1 =
         let uu____22787 = solve_and_commit env wl fail1  in
         match uu____22787 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___169_22800 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___169_22800.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_22800.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_22800.FStar_TypeChecker_Env.implicits)
             }
         | uu____22805 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___170_22809 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___170_22809.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___170_22809.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___170_22809.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____22835 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22835 with
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
            let uu___171_22938 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___171_22938.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___171_22938.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___171_22938.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22939 =
            let uu____22940 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22940  in
          if uu____22939
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22948 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22949 =
                       let uu____22950 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22950
                        in
                     FStar_Errors.diag uu____22948 uu____22949)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22954 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22955 =
                        let uu____22956 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22956
                         in
                      FStar_Errors.diag uu____22954 uu____22955)
                   else ();
                   (let uu____22959 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22959 "discharge_guard'"
                      env vc1);
                   (let uu____22960 = check_trivial vc1  in
                    match uu____22960 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22967 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22968 =
                                let uu____22969 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22969
                                 in
                              FStar_Errors.diag uu____22967 uu____22968)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22974 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22975 =
                                let uu____22976 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22976
                                 in
                              FStar_Errors.diag uu____22974 uu____22975)
                           else ();
                           (let vcs =
                              let uu____22987 = FStar_Options.use_tactics ()
                                 in
                              if uu____22987
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23006  ->
                                     (let uu____23008 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23008);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____23010 =
                                   let uu____23017 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23017)  in
                                 [uu____23010])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23051  ->
                                    match uu____23051 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____23062 = check_trivial goal1
                                           in
                                        (match uu____23062 with
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
                                                (let uu____23070 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23071 =
                                                   let uu____23072 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____23073 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23072 uu____23073
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23070 uu____23071)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23076 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23077 =
                                                   let uu____23078 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23078
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23076 uu____23077)
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
      let uu____23088 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23088 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23094 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23094
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23101 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23101 with
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
          let uu____23120 = FStar_Syntax_Unionfind.find u  in
          match uu____23120 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23123 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23141 = acc  in
          match uu____23141 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23227 = hd1  in
                   (match uu____23227 with
                    | (uu____23240,env,u,tm,k,r) ->
                        let uu____23246 = unresolved u  in
                        if uu____23246
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___172_23276 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___172_23276.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___172_23276.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___172_23276.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___172_23276.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___172_23276.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___172_23276.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___172_23276.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___172_23276.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___172_23276.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___172_23276.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___172_23276.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___172_23276.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___172_23276.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___172_23276.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___172_23276.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___172_23276.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___172_23276.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___172_23276.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___172_23276.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___172_23276.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___172_23276.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___172_23276.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___172_23276.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___172_23276.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___172_23276.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___172_23276.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___172_23276.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___172_23276.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___172_23276.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___172_23276.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___172_23276.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___172_23276.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___172_23276.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___172_23276.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___172_23276.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23279 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23279
                            then
                              let uu____23280 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23281 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23282 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23280 uu____23281 uu____23282
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23293 =
                                      let uu____23302 =
                                        let uu____23309 =
                                          let uu____23310 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23311 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23310 uu____23311
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23309, r)
                                         in
                                      [uu____23302]  in
                                    FStar_Errors.add_errors uu____23293);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___175_23325 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___175_23325.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___175_23325.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___175_23325.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23328 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23334  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23328 with
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
        let uu___176_23362 = g  in
        let uu____23363 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_23362.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_23362.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___176_23362.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23363
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
        let uu____23417 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23417 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23430 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23430
      | (reason,uu____23432,uu____23433,e,t,r)::uu____23437 ->
          let uu____23464 =
            let uu____23469 =
              let uu____23470 = FStar_Syntax_Print.term_to_string t  in
              let uu____23471 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23470 uu____23471
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23469)
             in
          FStar_Errors.raise_error uu____23464 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___177_23478 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___177_23478.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___177_23478.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___177_23478.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23501 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23501 with
      | FStar_Pervasives_Native.Some uu____23506 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23516 = try_teq false env t1 t2  in
        match uu____23516 with
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
        (let uu____23536 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23536
         then
           let uu____23537 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23538 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23537
             uu____23538
         else ());
        (let uu____23540 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23540 with
         | (prob,x) ->
             let g =
               let uu____23556 =
                 let uu____23559 = singleton' env prob true  in
                 solve_and_commit env uu____23559
                   (fun uu____23561  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23556  in
             ((let uu____23571 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23571
               then
                 let uu____23572 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23573 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23574 =
                   let uu____23575 = FStar_Util.must g  in
                   guard_to_string env uu____23575  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23572 uu____23573 uu____23574
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
        let uu____23603 = check_subtyping env t1 t2  in
        match uu____23603 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23622 =
              let uu____23623 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23623 g  in
            FStar_Pervasives_Native.Some uu____23622
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23635 = check_subtyping env t1 t2  in
        match uu____23635 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23654 =
              let uu____23655 =
                let uu____23656 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23656]  in
              close_guard env uu____23655 g  in
            FStar_Pervasives_Native.Some uu____23654
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23667 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23667
         then
           let uu____23668 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23669 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23668
             uu____23669
         else ());
        (let uu____23671 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23671 with
         | (prob,x) ->
             let g =
               let uu____23681 =
                 let uu____23684 = singleton' env prob false  in
                 solve_and_commit env uu____23684
                   (fun uu____23686  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23681  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23697 =
                      let uu____23698 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23698]  in
                    close_guard env uu____23697 g1  in
                  discharge_guard_nosmt env g2))
  