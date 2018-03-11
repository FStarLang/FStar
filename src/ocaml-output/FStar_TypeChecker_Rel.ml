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
            let uu____5346 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5346
            then FullMatch
            else
              (let uu____5348 =
                 let uu____5357 =
                   let uu____5360 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5360  in
                 let uu____5361 =
                   let uu____5364 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5364  in
                 (uu____5357, uu____5361)  in
               MisMatch uu____5348)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5370),FStar_Syntax_Syntax.Tm_uinst (g,uu____5372)) ->
            let uu____5381 = head_matches env f g  in
            FStar_All.pipe_right uu____5381 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5384 = FStar_Const.eq_const c d  in
            if uu____5384
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5391),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5393)) ->
            let uu____5442 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5442
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5449),FStar_Syntax_Syntax.Tm_refine (y,uu____5451)) ->
            let uu____5460 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5460 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5462),uu____5463) ->
            let uu____5468 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5468 head_match
        | (uu____5469,FStar_Syntax_Syntax.Tm_refine (x,uu____5471)) ->
            let uu____5476 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5476 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5477,FStar_Syntax_Syntax.Tm_type
           uu____5478) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5479,FStar_Syntax_Syntax.Tm_arrow uu____5480) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5609 =
                let uu____5610 = FStar_List.zip bs1 bs2  in
                let uu____5645 = head_matches env t12 t22  in
                FStar_List.fold_right
                  (fun uu____5654  ->
                     fun a  ->
                       match uu____5654 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5663  -> branch_matches env b1 b2))
                  uu____5610 uu____5645
                 in
              FStar_All.pipe_right uu____5609 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5670),FStar_Syntax_Syntax.Tm_app (head',uu____5672))
            ->
            let uu____5713 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5713 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5715),uu____5716) ->
            let uu____5737 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5737 head_match
        | (uu____5738,FStar_Syntax_Syntax.Tm_app (head1,uu____5740)) ->
            let uu____5761 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5761 head_match
        | uu____5762 ->
            let uu____5767 =
              let uu____5776 = delta_depth_of_term env t11  in
              let uu____5779 = delta_depth_of_term env t21  in
              (uu____5776, uu____5779)  in
            MisMatch uu____5767

and (branch_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch -> match_result)
  =
  fun env  ->
    fun b1  ->
      fun b2  ->
        let related_by f o1 o2 =
          match (o1, o2) with
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
              true
          | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y)
              -> f x y
          | (uu____5831,uu____5832) -> false  in
        let uu____5841 = b1  in
        match uu____5841 with
        | (p1,w1,t1) ->
            let uu____5861 = b2  in
            (match uu____5861 with
             | (p2,w2,t2) ->
                 let uu____5881 = FStar_Syntax_Syntax.eq_pat p1 p2  in
                 if uu____5881
                 then
                   let uu____5882 =
                     (let uu____5885 = FStar_Syntax_Util.eq_tm t1 t2  in
                      uu____5885 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5894 =
                                 FStar_Syntax_Util.eq_tm t11 t21  in
                               uu____5894 = FStar_Syntax_Util.Equal) w1 w2)
                      in
                   (if uu____5882
                    then FullMatch
                    else
                      MisMatch
                        (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None))
                 else
                   MisMatch
                     (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None))

let head_matches_delta :
  'Auu____5910 .
    FStar_TypeChecker_Env.env ->
      'Auu____5910 ->
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
            let uu____5943 = FStar_Syntax_Util.head_and_args t  in
            match uu____5943 with
            | (head1,uu____5961) ->
                let uu____5982 =
                  let uu____5983 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5983.FStar_Syntax_Syntax.n  in
                (match uu____5982 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5989 =
                       let uu____5990 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5990 FStar_Option.isSome
                        in
                     if uu____5989
                     then
                       let uu____6009 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6009
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____6013 -> FStar_Pervasives_Native.None)
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6116)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6134 =
                     let uu____6143 = maybe_inline t11  in
                     let uu____6146 = maybe_inline t21  in
                     (uu____6143, uu____6146)  in
                   match uu____6134 with
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
                (uu____6183,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6201 =
                     let uu____6210 = maybe_inline t11  in
                     let uu____6213 = maybe_inline t21  in
                     (uu____6210, uu____6213)  in
                   match uu____6201 with
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
                let uu____6256 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6256 with
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
                let uu____6279 =
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
                (match uu____6279 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6303 -> fail1 r
            | uu____6312 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6325 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6325
           then
             let uu____6326 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6327 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6328 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6326
               uu____6327 uu____6328
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6368 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6404 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___104_6416  ->
    match uu___104_6416 with
    | T (t,uu____6418) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6434 = FStar_Syntax_Util.type_u ()  in
      match uu____6434 with
      | (t,uu____6440) ->
          let uu____6441 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6441
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6452 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6452 FStar_Pervasives_Native.fst
  
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
        let uu____6516 = head_matches env t1 t'  in
        match uu____6516 with
        | MisMatch uu____6517 -> false
        | uu____6526 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6622,imp),T (t2,uu____6625)) -> (t2, imp)
                     | uu____6644 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6711  ->
                    match uu____6711 with
                    | (t2,uu____6725) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6768 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6768 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6843))::tcs2) ->
                       aux
                         (((let uu___129_6878 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_6878.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_6878.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6896 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___105_6949 =
                 match uu___105_6949 with
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
               let uu____7066 = decompose1 [] bs1  in
               (rebuild, matches, uu____7066))
      | uu____7115 ->
          let rebuild uu___106_7121 =
            match uu___106_7121 with
            | [] -> t1
            | uu____7124 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___107_7155  ->
    match uu___107_7155 with
    | T (t,uu____7157) -> t
    | uu____7166 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___108_7169  ->
    match uu___108_7169 with
    | T (t,uu____7171) -> FStar_Syntax_Syntax.as_arg t
    | uu____7180 -> failwith "Impossible"
  
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
              | (uu____7296,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7321 = new_uvar r scope1 k  in
                  (match uu____7321 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7339 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7356 =
                         let uu____7357 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7357
                          in
                       ((T (gi_xs, mk_kind)), uu____7356))
              | (uu____7370,uu____7371,C uu____7372) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7519 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7536;
                         FStar_Syntax_Syntax.vars = uu____7537;_})
                        ->
                        let uu____7560 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7560 with
                         | (T (gi_xs,uu____7584),prob) ->
                             let uu____7594 =
                               let uu____7595 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7595
                                in
                             (uu____7594, [prob])
                         | uu____7598 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7613;
                         FStar_Syntax_Syntax.vars = uu____7614;_})
                        ->
                        let uu____7637 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7637 with
                         | (T (gi_xs,uu____7661),prob) ->
                             let uu____7671 =
                               let uu____7672 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7672
                                in
                             (uu____7671, [prob])
                         | uu____7675 -> failwith "impossible")
                    | (uu____7686,uu____7687,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7689;
                         FStar_Syntax_Syntax.vars = uu____7690;_})
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
                        let uu____7821 =
                          let uu____7830 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7830 FStar_List.unzip
                           in
                        (match uu____7821 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7884 =
                                 let uu____7885 =
                                   let uu____7888 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7888 un_T  in
                                 let uu____7889 =
                                   let uu____7898 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7898
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7885;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7889;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7884
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7907 ->
                        let uu____7920 = sub_prob scope1 args q  in
                        (match uu____7920 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7519 with
                   | (tc,probs) ->
                       let uu____7951 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8014,uu____8015),T
                            (t,uu____8017)) ->
                             let b1 =
                               ((let uu___130_8054 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_8054.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_8054.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8055 =
                               let uu____8062 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8062 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8055)
                         | uu____8097 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7951 with
                        | (bopt,scope2,args1) ->
                            let uu____8181 = aux scope2 args1 qs2  in
                            (match uu____8181 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8219 =
                                           let uu____8222 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8222  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8219
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
                                         let uu____8247 =
                                           let uu____8250 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8251 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8250 :: uu____8251  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8247
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
  'Auu____8320 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8320)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8320)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___131_8341 = p  in
      let uu____8346 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8347 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___131_8341.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8346;
        FStar_TypeChecker_Common.relation =
          (uu___131_8341.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8347;
        FStar_TypeChecker_Common.element =
          (uu___131_8341.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___131_8341.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___131_8341.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___131_8341.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___131_8341.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___131_8341.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8359 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8359
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8368 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8388 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8388 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8398 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8398 with
           | (lh,uu____8418) ->
               let uu____8439 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8439 with
                | (rh,uu____8459) ->
                    let uu____8480 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8497,FStar_Syntax_Syntax.Tm_uvar uu____8498)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8535,uu____8536)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8557,FStar_Syntax_Syntax.Tm_uvar uu____8558)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8579,uu____8580)
                          ->
                          let uu____8597 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8597 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8646 ->
                                    let rank =
                                      let uu____8654 = is_top_level_prob prob
                                         in
                                      if uu____8654
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8656 =
                                      let uu___132_8661 = tp  in
                                      let uu____8666 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___132_8661.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___132_8661.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___132_8661.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8666;
                                        FStar_TypeChecker_Common.element =
                                          (uu___132_8661.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___132_8661.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___132_8661.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___132_8661.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___132_8661.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___132_8661.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8656)))
                      | (uu____8677,FStar_Syntax_Syntax.Tm_uvar uu____8678)
                          ->
                          let uu____8695 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8695 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8744 ->
                                    let uu____8751 =
                                      let uu___133_8758 = tp  in
                                      let uu____8763 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___133_8758.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8763;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___133_8758.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___133_8758.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___133_8758.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___133_8758.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___133_8758.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___133_8758.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___133_8758.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___133_8758.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8751)))
                      | (uu____8780,uu____8781) -> (rigid_rigid, tp)  in
                    (match uu____8480 with
                     | (rank,tp1) ->
                         let uu____8800 =
                           FStar_All.pipe_right
                             (let uu___134_8806 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___134_8806.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___134_8806.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___134_8806.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___134_8806.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___134_8806.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___134_8806.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___134_8806.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___134_8806.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___134_8806.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8800))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8816 =
            FStar_All.pipe_right
              (let uu___135_8822 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___135_8822.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___135_8822.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___135_8822.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___135_8822.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___135_8822.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___135_8822.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___135_8822.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___135_8822.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___135_8822.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8816)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8877 probs =
      match uu____8877 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8930 = rank wl hd1  in
               (match uu____8930 with
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
    match projectee with | UDeferred _0 -> true | uu____9037 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9049 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9061 -> false
  
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
                        let uu____9101 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9101 with
                        | (k,uu____9107) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9117 -> false)))
            | uu____9118 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9166 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9172 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9172 = (Prims.parse_int "0")))
                           in
                        if uu____9166 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9186 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9192 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9192 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9186)
               in
            let uu____9193 = filter1 u12  in
            let uu____9196 = filter1 u22  in (uu____9193, uu____9196)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9219 = filter_out_common_univs us1 us2  in
                (match uu____9219 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9272 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9272 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9275 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9285 =
                          let uu____9286 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9287 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9286
                            uu____9287
                           in
                        UFailed uu____9285))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9307 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9307 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9329 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9329 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9332 ->
                let uu____9337 =
                  let uu____9338 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9339 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9338
                    uu____9339 msg
                   in
                UFailed uu____9337
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9340,uu____9341) ->
              let uu____9342 =
                let uu____9343 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9344 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9343 uu____9344
                 in
              failwith uu____9342
          | (FStar_Syntax_Syntax.U_unknown ,uu____9345) ->
              let uu____9346 =
                let uu____9347 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9348 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9347 uu____9348
                 in
              failwith uu____9346
          | (uu____9349,FStar_Syntax_Syntax.U_bvar uu____9350) ->
              let uu____9351 =
                let uu____9352 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9353 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9352 uu____9353
                 in
              failwith uu____9351
          | (uu____9354,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9355 =
                let uu____9356 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9357 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9356 uu____9357
                 in
              failwith uu____9355
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9381 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9381
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9403 = occurs_univ v1 u3  in
              if uu____9403
              then
                let uu____9404 =
                  let uu____9405 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9406 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9405 uu____9406
                   in
                try_umax_components u11 u21 uu____9404
              else
                (let uu____9408 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9408)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9428 = occurs_univ v1 u3  in
              if uu____9428
              then
                let uu____9429 =
                  let uu____9430 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9431 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9430 uu____9431
                   in
                try_umax_components u11 u21 uu____9429
              else
                (let uu____9433 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9433)
          | (FStar_Syntax_Syntax.U_max uu____9442,uu____9443) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9449 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9449
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9451,FStar_Syntax_Syntax.U_max uu____9452) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9458 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9458
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9460,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9461,FStar_Syntax_Syntax.U_name
             uu____9462) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9463) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9464) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9465,FStar_Syntax_Syntax.U_succ
             uu____9466) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9467,FStar_Syntax_Syntax.U_zero
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
      let uu____9553 = bc1  in
      match uu____9553 with
      | (bs1,mk_cod1) ->
          let uu____9594 = bc2  in
          (match uu____9594 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9698 = aux xs ys  in
                     (match uu____9698 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9781 =
                       let uu____9788 = mk_cod1 xs  in ([], uu____9788)  in
                     let uu____9791 =
                       let uu____9798 = mk_cod2 ys  in ([], uu____9798)  in
                     (uu____9781, uu____9791)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9909 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9909
       then
         let uu____9910 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9910
       else ());
      (let uu____9912 = next_prob probs  in
       match uu____9912 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___136_9933 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___136_9933.wl_deferred);
               ctr = (uu___136_9933.ctr);
               defer_ok = (uu___136_9933.defer_ok);
               smt_ok = (uu___136_9933.smt_ok);
               tcenv = (uu___136_9933.tcenv)
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
                  let uu____9944 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9944 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9949 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9949 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9954,uu____9955) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9972 ->
                let uu____9981 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10040  ->
                          match uu____10040 with
                          | (c,uu____10048,uu____10049) -> c < probs.ctr))
                   in
                (match uu____9981 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10090 =
                            FStar_List.map
                              (fun uu____10105  ->
                                 match uu____10105 with
                                 | (uu____10116,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10090
                      | uu____10119 ->
                          let uu____10128 =
                            let uu___137_10129 = probs  in
                            let uu____10130 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10151  ->
                                      match uu____10151 with
                                      | (uu____10158,uu____10159,y) -> y))
                               in
                            {
                              attempting = uu____10130;
                              wl_deferred = rest;
                              ctr = (uu___137_10129.ctr);
                              defer_ok = (uu___137_10129.defer_ok);
                              smt_ok = (uu___137_10129.smt_ok);
                              tcenv = (uu___137_10129.tcenv)
                            }  in
                          solve env uu____10128))))

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
            let uu____10166 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10166 with
            | USolved wl1 ->
                let uu____10168 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10168
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
                  let uu____10214 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10214 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10217 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10229;
                  FStar_Syntax_Syntax.vars = uu____10230;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10233;
                  FStar_Syntax_Syntax.vars = uu____10234;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10248,uu____10249) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10256,FStar_Syntax_Syntax.Tm_uinst uu____10257) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10264 -> USolved wl

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
            ((let uu____10274 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10274
              then
                let uu____10275 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10275 msg
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
        (let uu____10284 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10284
         then
           let uu____10285 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10285
         else ());
        (let uu____10287 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10287 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10349 = head_matches_delta env () t1 t2  in
               match uu____10349 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10390 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10439 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10454 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10455 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10454, uu____10455)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10460 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10461 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10460, uu____10461)
                           in
                        (match uu____10439 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10487 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10487
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10518 =
                                    let uu____10527 =
                                      let uu____10530 =
                                        let uu____10533 =
                                          let uu____10534 =
                                            let uu____10541 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10541)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10534
                                           in
                                        FStar_Syntax_Syntax.mk uu____10533
                                         in
                                      uu____10530
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10549 =
                                      let uu____10552 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10552]  in
                                    (uu____10527, uu____10549)  in
                                  FStar_Pervasives_Native.Some uu____10518
                              | (uu____10565,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10567)) ->
                                  let uu____10572 =
                                    let uu____10579 =
                                      let uu____10582 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10582]  in
                                    (t11, uu____10579)  in
                                  FStar_Pervasives_Native.Some uu____10572
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10592),uu____10593) ->
                                  let uu____10598 =
                                    let uu____10605 =
                                      let uu____10608 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10608]  in
                                    (t21, uu____10605)  in
                                  FStar_Pervasives_Native.Some uu____10598
                              | uu____10617 ->
                                  let uu____10622 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10622 with
                                   | (head1,uu____10646) ->
                                       let uu____10667 =
                                         let uu____10668 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10668.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10667 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10679;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10681;_}
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
                                        | uu____10688 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10701) ->
                  let uu____10726 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___109_10752  ->
                            match uu___109_10752 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10759 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10759 with
                                      | (u',uu____10775) ->
                                          let uu____10796 =
                                            let uu____10797 = whnf env u'  in
                                            uu____10797.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10796 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10801) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10826 -> false))
                                 | uu____10827 -> false)
                            | uu____10830 -> false))
                     in
                  (match uu____10726 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10864 tps =
                         match uu____10864 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10912 =
                                    let uu____10921 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10921  in
                                  (match uu____10912 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10956 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10965 =
                         let uu____10974 =
                           let uu____10981 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10981, [])  in
                         make_lower_bound uu____10974 lower_bounds  in
                       (match uu____10965 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10993 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10993
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
                            ((let uu____11013 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11013
                              then
                                let wl' =
                                  let uu___138_11015 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___138_11015.wl_deferred);
                                    ctr = (uu___138_11015.ctr);
                                    defer_ok = (uu___138_11015.defer_ok);
                                    smt_ok = (uu___138_11015.smt_ok);
                                    tcenv = (uu___138_11015.tcenv)
                                  }  in
                                let uu____11016 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11016
                              else ());
                             (let uu____11018 =
                                solve_t env eq_prob
                                  (let uu___139_11020 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___139_11020.wl_deferred);
                                     ctr = (uu___139_11020.ctr);
                                     defer_ok = (uu___139_11020.defer_ok);
                                     smt_ok = (uu___139_11020.smt_ok);
                                     tcenv = (uu___139_11020.tcenv)
                                   })
                                 in
                              match uu____11018 with
                              | Success uu____11023 ->
                                  let wl1 =
                                    let uu___140_11025 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___140_11025.wl_deferred);
                                      ctr = (uu___140_11025.ctr);
                                      defer_ok = (uu___140_11025.defer_ok);
                                      smt_ok = (uu___140_11025.smt_ok);
                                      tcenv = (uu___140_11025.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11027 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11032 -> FStar_Pervasives_Native.None))))
              | uu____11033 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11042 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11042
         then
           let uu____11043 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11043
         else ());
        (let uu____11045 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11045 with
         | (u,args) ->
             let uu____11084 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11084 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____11125 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____11125 with
                    | (h1,args1) ->
                        let uu____11166 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11166 with
                         | (h2,uu____11186) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11213 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11213
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11231 =
                                          let uu____11234 =
                                            let uu____11235 =
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
                                                   _0_53) uu____11235
                                             in
                                          [uu____11234]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11231))
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
                                       (let uu____11268 =
                                          let uu____11271 =
                                            let uu____11272 =
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
                                                   _0_54) uu____11272
                                             in
                                          [uu____11271]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11268))
                                  else FStar_Pervasives_Native.None
                              | uu____11286 -> FStar_Pervasives_Native.None))
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
                             let uu____11376 =
                               let uu____11385 =
                                 let uu____11388 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11388  in
                               (uu____11385, m1)  in
                             FStar_Pervasives_Native.Some uu____11376)
                    | (uu____11401,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11403)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11451),uu____11452) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11499 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11552) ->
                       let uu____11577 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___110_11603  ->
                                 match uu___110_11603 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11610 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11610 with
                                           | (u',uu____11626) ->
                                               let uu____11647 =
                                                 let uu____11648 =
                                                   whnf env u'  in
                                                 uu____11648.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11647 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11652) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11677 -> false))
                                      | uu____11678 -> false)
                                 | uu____11681 -> false))
                          in
                       (match uu____11577 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11719 tps =
                              match uu____11719 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11781 =
                                         let uu____11792 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11792  in
                                       (match uu____11781 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11843 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11854 =
                              let uu____11865 =
                                let uu____11874 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11874, [])  in
                              make_upper_bound uu____11865 upper_bounds  in
                            (match uu____11854 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11888 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11888
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
                                 ((let uu____11914 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11914
                                   then
                                     let wl' =
                                       let uu___141_11916 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___141_11916.wl_deferred);
                                         ctr = (uu___141_11916.ctr);
                                         defer_ok = (uu___141_11916.defer_ok);
                                         smt_ok = (uu___141_11916.smt_ok);
                                         tcenv = (uu___141_11916.tcenv)
                                       }  in
                                     let uu____11917 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11917
                                   else ());
                                  (let uu____11919 =
                                     solve_t env eq_prob
                                       (let uu___142_11921 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___142_11921.wl_deferred);
                                          ctr = (uu___142_11921.ctr);
                                          defer_ok =
                                            (uu___142_11921.defer_ok);
                                          smt_ok = (uu___142_11921.smt_ok);
                                          tcenv = (uu___142_11921.tcenv)
                                        })
                                      in
                                   match uu____11919 with
                                   | Success uu____11924 ->
                                       let wl1 =
                                         let uu___143_11926 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___143_11926.wl_deferred);
                                           ctr = (uu___143_11926.ctr);
                                           defer_ok =
                                             (uu___143_11926.defer_ok);
                                           smt_ok = (uu___143_11926.smt_ok);
                                           tcenv = (uu___143_11926.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11928 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11933 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11934 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____12009 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12009
                      then
                        let uu____12010 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____12010
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___144_12064 = hd1  in
                      let uu____12065 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_12064.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_12064.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12065
                      }  in
                    let hd21 =
                      let uu___145_12069 = hd2  in
                      let uu____12070 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_12069.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_12069.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12070
                      }  in
                    let prob =
                      let uu____12074 =
                        let uu____12079 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12079 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____12074
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____12090 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12090
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____12094 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____12094 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12132 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____12137 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____12132 uu____12137
                            in
                         ((let uu____12147 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12147
                           then
                             let uu____12148 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____12149 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12148 uu____12149
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail1 -> fail1)
                | uu____12172 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____12182 = aux scope env [] bs1 bs2  in
              match uu____12182 with
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
        (let uu____12207 = compress_tprob wl problem  in
         solve_t' env uu____12207 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12241 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12241 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12272,uu____12273) ->
                    let rec may_relate head3 =
                      let uu____12298 =
                        let uu____12299 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12299.FStar_Syntax_Syntax.n  in
                      match uu____12298 with
                      | FStar_Syntax_Syntax.Tm_name uu____12302 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12303 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12326;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____12327;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12330;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12331;
                            FStar_Syntax_Syntax.fv_qual = uu____12332;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12336,uu____12337) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12379) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12385) ->
                          may_relate t
                      | uu____12390 -> false  in
                    let uu____12391 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12391
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
                                 let uu____12408 =
                                   let uu____12409 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12409 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12408
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____12411 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____12411
                    else
                      (let uu____12413 =
                         let uu____12414 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12415 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12414 uu____12415
                          in
                       giveup env1 uu____12413 orig)
                | (uu____12416,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___146_12430 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___146_12430.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___146_12430.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___146_12430.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___146_12430.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___146_12430.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___146_12430.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___146_12430.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___146_12430.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12431,FStar_Pervasives_Native.None ) ->
                    ((let uu____12443 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12443
                      then
                        let uu____12444 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12445 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12446 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12447 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12444
                          uu____12445 uu____12446 uu____12447
                      else ());
                     (let uu____12449 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12449 with
                      | (head11,args1) ->
                          let uu____12486 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12486 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12540 =
                                   let uu____12541 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12542 = args_to_string args1  in
                                   let uu____12543 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12544 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12541 uu____12542 uu____12543
                                     uu____12544
                                    in
                                 giveup env1 uu____12540 orig
                               else
                                 (let uu____12546 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12552 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12552 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12546
                                  then
                                    let uu____12553 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12553 with
                                    | USolved wl2 ->
                                        let uu____12555 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12555
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12559 =
                                       base_and_refinement env1 t1  in
                                     match uu____12559 with
                                     | (base1,refinement1) ->
                                         let uu____12584 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12584 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____12641 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____12641 with
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
                                                            (fun uu____12663 
                                                               ->
                                                               fun
                                                                 uu____12664 
                                                                 ->
                                                                 match 
                                                                   (uu____12663,
                                                                    uu____12664)
                                                                 with
                                                                 | ((a,uu____12682),
                                                                    (a',uu____12684))
                                                                    ->
                                                                    let uu____12693
                                                                    =
                                                                    let uu____12698
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12698
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
                                                                    uu____12693)
                                                            args1 args2
                                                           in
                                                        let formula =
                                                          let uu____12704 =
                                                            FStar_List.map
                                                              (fun p  ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____12704
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
                                               | uu____12710 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___147_12746 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___147_12746.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____12779 =
           match uu____12779 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____12821 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____12821 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____12917  ->
                      let uu____12918 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____12918);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____12986  ->
                                match uu____12986 with
                                | (x,imp) ->
                                    let uu____12997 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____12997, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____13010 = FStar_Syntax_Util.type_u ()  in
                        match uu____13010 with
                        | (t1,uu____13016) ->
                            let uu____13017 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____13017
                         in
                      let uu____13022 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____13022 with
                       | (t',tm_u1) ->
                           let uu____13035 = destruct_flex_t t'  in
                           (match uu____13035 with
                            | (uu____13072,u1,k1,uu____13075) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____13134 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13134
                                   in
                                let sol =
                                  let uu____13138 =
                                    let uu____13147 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13147)  in
                                  TERM uu____13138  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____13282  ->
                            let uu____13283 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____13284 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13283 uu____13284);
                       (let uu____13297 = pat_var_opt env pat_args hd1  in
                        match uu____13297 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____13317  ->
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
                                       (fun uu____13360  ->
                                          match uu____13360 with
                                          | (x,uu____13366) ->
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
                                 (fun uu____13381  ->
                                    let uu____13382 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____13395 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____13382
                                      uu____13395);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____13399 =
                                  let uu____13400 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____13400  in
                                if uu____13399
                                then
                                  (debug1
                                     (fun uu____13412  ->
                                        let uu____13413 =
                                          let uu____13416 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____13429 =
                                            let uu____13432 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____13433 =
                                              let uu____13436 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____13437 =
                                                let uu____13440 =
                                                  names_to_string fvs  in
                                                let uu____13441 =
                                                  let uu____13444 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____13444]  in
                                                uu____13440 :: uu____13441
                                                 in
                                              uu____13436 :: uu____13437  in
                                            uu____13432 :: uu____13433  in
                                          uu____13416 :: uu____13429  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____13413);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____13446 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____13449 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____13446 (formal ::
                                     pattern_vars) uu____13449 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____13456::uu____13457) ->
                      let uu____13488 =
                        let uu____13501 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____13501  in
                      (match uu____13488 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____13540 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____13547::uu____13548,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____13571 =
                 let uu____13584 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____13584  in
               (match uu____13571 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____13620  ->
                          let uu____13621 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____13622 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____13623 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____13624 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____13621 uu____13622 uu____13623 uu____13624);
                     (let uu____13625 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____13628 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____13625 [] uu____13628 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____13662 = lhs  in
           match uu____13662 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____13672 ->
                     let uu____13673 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____13673 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____13696 = p  in
           match uu____13696 with
           | (((u,k),xs,c),ps,(h,uu____13707,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13789 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____13789 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____13812 = h gs_xs  in
                      let uu____13813 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         in
                      FStar_Syntax_Util.abs xs1 uu____13812 uu____13813  in
                    ((let uu____13819 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13819
                      then
                        let uu____13820 =
                          let uu____13823 =
                            let uu____13824 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____13824
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____13829 =
                            let uu____13832 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____13833 =
                              let uu____13836 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____13837 =
                                let uu____13840 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____13841 =
                                  let uu____13844 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____13845 =
                                    let uu____13848 =
                                      let uu____13849 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____13849
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____13854 =
                                      let uu____13857 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____13857]  in
                                    uu____13848 :: uu____13854  in
                                  uu____13844 :: uu____13845  in
                                uu____13840 :: uu____13841  in
                              uu____13836 :: uu____13837  in
                            uu____13832 :: uu____13833  in
                          uu____13823 :: uu____13829  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____13820
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___111_13879 =
           match uu___111_13879 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____13911 = p  in
           match uu____13911 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14002 = FStar_List.nth ps i  in
               (match uu____14002 with
                | (pi,uu____14006) ->
                    let uu____14011 = FStar_List.nth xs i  in
                    (match uu____14011 with
                     | (xi,uu____14023) ->
                         let rec gs k =
                           let uu____14036 =
                             let uu____14049 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____14049  in
                           match uu____14036 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____14124)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____14137 = new_uvar r xs k_a  in
                                     (match uu____14137 with
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
                                          let uu____14159 = aux subst2 tl1
                                             in
                                          (match uu____14159 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____14186 =
                                                 let uu____14189 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____14189 :: gi_xs'  in
                                               let uu____14190 =
                                                 let uu____14193 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____14193 :: gi_ps'  in
                                               (uu____14186, uu____14190)))
                                  in
                               aux [] bs
                            in
                         let uu____14198 =
                           let uu____14199 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____14199
                            in
                         if uu____14198
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____14203 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____14203 with
                            | (g_xs,uu____14215) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____14226 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____14227 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_58  ->
                                         FStar_Pervasives_Native.Some _0_58)
                                     in
                                  FStar_Syntax_Util.abs xs uu____14226
                                    uu____14227
                                   in
                                let sub1 =
                                  let uu____14233 =
                                    let uu____14238 = p_scope orig  in
                                    let uu____14239 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____14242 =
                                      let uu____14245 =
                                        FStar_List.map
                                          (fun uu____14260  ->
                                             match uu____14260 with
                                             | (uu____14269,uu____14270,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____14245  in
                                    mk_problem uu____14238 orig uu____14239
                                      (p_rel orig) uu____14242
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_59  ->
                                       FStar_TypeChecker_Common.TProb _0_59)
                                    uu____14233
                                   in
                                ((let uu____14285 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14285
                                  then
                                    let uu____14286 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____14287 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____14286 uu____14287
                                  else ());
                                 (let wl2 =
                                    let uu____14290 =
                                      let uu____14293 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____14293
                                       in
                                    solve_prob orig uu____14290
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____14302 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_60  ->
                                       FStar_Pervasives_Native.Some _0_60)
                                    uu____14302)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____14333 = lhs  in
           match uu____14333 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____14369 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____14369 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____14402 =
                         let uu____14449 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____14449)  in
                       FStar_Pervasives_Native.Some uu____14402
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____14593 =
                            let uu____14600 =
                              let uu____14601 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____14601.FStar_Syntax_Syntax.n  in
                            (uu____14600, args)  in
                          match uu____14593 with
                          | (uu____14612,[]) ->
                              let uu____14615 =
                                let uu____14626 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____14626)  in
                              FStar_Pervasives_Native.Some uu____14615
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____14647,uu____14648) ->
                              let uu____14669 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14669 with
                               | (uv1,uv_args) ->
                                   let uu____14712 =
                                     let uu____14713 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14713.FStar_Syntax_Syntax.n  in
                                   (match uu____14712 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14723) ->
                                        let uu____14748 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14748 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14775  ->
                                                       let uu____14776 =
                                                         let uu____14777 =
                                                           let uu____14778 =
                                                             let uu____14783
                                                               =
                                                               let uu____14784
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14784
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14783
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14778
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14777
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14776))
                                                in
                                             let c1 =
                                               let uu____14794 =
                                                 let uu____14795 =
                                                   let uu____14800 =
                                                     let uu____14801 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14801
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14800
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14795
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14794
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14814 =
                                                 let uu____14817 =
                                                   let uu____14818 =
                                                     let uu____14821 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14821
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14818
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14817
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14814
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14840 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____14845,uu____14846) ->
                              let uu____14865 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14865 with
                               | (uv1,uv_args) ->
                                   let uu____14908 =
                                     let uu____14909 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14909.FStar_Syntax_Syntax.n  in
                                   (match uu____14908 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14919) ->
                                        let uu____14944 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14944 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14971  ->
                                                       let uu____14972 =
                                                         let uu____14973 =
                                                           let uu____14974 =
                                                             let uu____14979
                                                               =
                                                               let uu____14980
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14980
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14979
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14974
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14973
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14972))
                                                in
                                             let c1 =
                                               let uu____14990 =
                                                 let uu____14991 =
                                                   let uu____14996 =
                                                     let uu____14997 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14997
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14996
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14991
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14990
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15010 =
                                                 let uu____15013 =
                                                   let uu____15014 =
                                                     let uu____15017 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15017
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15014
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15013
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15010
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15036 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____15043) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____15084 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____15084
                                  (fun _0_61  ->
                                     FStar_Pervasives_Native.Some _0_61)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____15120 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____15120 with
                                   | (args1,rest) ->
                                       let uu____15149 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____15149 with
                                        | (xs2,c2) ->
                                            let uu____15162 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____15162
                                              (fun uu____15186  ->
                                                 match uu____15186 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____15226 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____15226 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15294 =
                                         let uu____15299 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____15299
                                          in
                                       FStar_All.pipe_right uu____15294
                                         (fun _0_62  ->
                                            FStar_Pervasives_Native.Some
                                              _0_62))
                          | uu____15314 ->
                              let uu____15321 =
                                let uu____15326 =
                                  let uu____15327 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____15328 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____15329 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____15327 uu____15328 uu____15329
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____15326)
                                 in
                              FStar_Errors.raise_error uu____15321
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____15336 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____15336
                          (fun uu____15391  ->
                             match uu____15391 with
                             | (xs1,c1) ->
                                 let uu____15440 =
                                   let uu____15481 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____15481)
                                    in
                                 FStar_Pervasives_Native.Some uu____15440))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____15602 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____15616 = project orig env wl1 i st  in
                      match uu____15616 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15630) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____15645 = imitate orig env wl1 st  in
                   match uu____15645 with
                   | Failed uu____15650 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____15681 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____15681 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____15704 = forced_lhs_pattern  in
                     (match uu____15704 with
                      | (lhs_t,uu____15706,uu____15707,uu____15708) ->
                          ((let uu____15710 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15710
                            then
                              let uu____15711 = lhs1  in
                              match uu____15711 with
                              | (t0,uu____15713,uu____15714,uu____15715) ->
                                  let uu____15716 = forced_lhs_pattern  in
                                  (match uu____15716 with
                                   | (t11,uu____15718,uu____15719,uu____15720)
                                       ->
                                       let uu____15721 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____15722 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____15721 uu____15722)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____15730 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____15730
                            then
                              ((let uu____15732 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15732
                                then
                                  let uu____15733 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____15734 = names_to_string rhs_vars
                                     in
                                  let uu____15735 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____15733 uu____15734 uu____15735
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____15739 =
                                  let uu____15740 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____15740 wl2  in
                                match uu____15739 with
                                | Failed uu____15741 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____15750 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15750
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____15763 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____15763 with
                 | (hd1,uu____15779) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____15800 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____15813 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____15814 -> true
                      | uu____15831 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____15835 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____15835
                          then true
                          else
                            ((let uu____15838 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____15838
                              then
                                let uu____15839 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____15839
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
                    let uu____15859 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____15859 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____15872 =
                             let uu____15873 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____15873
                              in
                           giveup_or_defer1 orig uu____15872
                         else
                           (let uu____15875 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____15875
                            then
                              let uu____15876 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____15876
                               then
                                 let uu____15877 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____15877
                               else
                                 ((let uu____15882 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____15882
                                   then
                                     let uu____15883 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____15884 = names_to_string fvs1
                                        in
                                     let uu____15885 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____15883 uu____15884 uu____15885
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
                                (let uu____15889 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____15889
                                 then
                                   ((let uu____15891 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____15891
                                     then
                                       let uu____15892 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____15893 = names_to_string fvs1
                                          in
                                       let uu____15894 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____15892 uu____15893 uu____15894
                                     else ());
                                    (let uu____15896 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____15896))
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
                      (let uu____15907 =
                         let uu____15908 = FStar_Syntax_Free.names t1  in
                         check_head uu____15908 t2  in
                       if uu____15907
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____15919 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15919
                           then
                             let uu____15920 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____15921 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____15920 uu____15921
                           else ());
                          (let uu____15929 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____15929))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____16006 uu____16007 r =
                match (uu____16006, uu____16007) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____16205 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____16205
                    then
                      let uu____16206 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____16206
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____16230 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____16230
                        then
                          let uu____16231 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____16232 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____16233 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____16234 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____16235 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16231 uu____16232 uu____16233 uu____16234
                            uu____16235
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____16295 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____16295 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____16309 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____16309 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____16363 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____16363
                                      in
                                   let uu____16366 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____16366 k3)
                            else
                              (let uu____16370 =
                                 let uu____16371 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____16372 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____16373 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____16371 uu____16372 uu____16373
                                  in
                               failwith uu____16370)
                           in
                        let uu____16374 =
                          let uu____16381 =
                            let uu____16394 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____16394  in
                          match uu____16381 with
                          | (bs,k1') ->
                              let uu____16419 =
                                let uu____16432 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____16432
                                 in
                              (match uu____16419 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____16460 =
                                       let uu____16465 = p_scope orig  in
                                       mk_problem uu____16465 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_63  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_63) uu____16460
                                      in
                                   let uu____16470 =
                                     let uu____16475 =
                                       let uu____16476 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____16476.FStar_Syntax_Syntax.n  in
                                     let uu____16479 =
                                       let uu____16480 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____16480.FStar_Syntax_Syntax.n  in
                                     (uu____16475, uu____16479)  in
                                   (match uu____16470 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____16489,uu____16490) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____16493,FStar_Syntax_Syntax.Tm_type
                                       uu____16494) -> (k2'_ys, [sub_prob])
                                    | uu____16497 ->
                                        let uu____16502 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____16502 with
                                         | (t,uu____16514) ->
                                             let uu____16515 =
                                               new_uvar r zs t  in
                                             (match uu____16515 with
                                              | (k_zs,uu____16527) ->
                                                  let kprob =
                                                    let uu____16529 =
                                                      let uu____16534 =
                                                        p_scope orig  in
                                                      mk_problem uu____16534
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_64  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_64) uu____16529
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____16374 with
                        | (k_u',sub_probs) ->
                            let uu____16547 =
                              let uu____16558 =
                                let uu____16559 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____16559
                                 in
                              let uu____16568 =
                                let uu____16571 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____16571  in
                              let uu____16574 =
                                let uu____16577 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____16577  in
                              (uu____16558, uu____16568, uu____16574)  in
                            (match uu____16547 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____16596 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____16596 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____16615 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____16615
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
                                            let uu____16619 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____16619 with
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
              let solve_one_pat uu____16672 uu____16673 =
                match (uu____16672, uu____16673) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____16791 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____16791
                      then
                        let uu____16792 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____16793 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____16792 uu____16793
                      else ());
                     (let uu____16795 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____16795
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____16814  ->
                               fun uu____16815  ->
                                 match (uu____16814, uu____16815) with
                                 | ((a,uu____16833),(t21,uu____16835)) ->
                                     let uu____16844 =
                                       let uu____16849 = p_scope orig  in
                                       let uu____16850 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____16849 orig
                                         uu____16850
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____16844
                                       (fun _0_65  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_65)) xs args2
                           in
                        let guard =
                          let uu____16856 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____16856  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____16871 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____16871 with
                         | (occurs_ok,uu____16879) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____16887 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____16887
                             then
                               let sol =
                                 let uu____16889 =
                                   let uu____16898 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____16898)  in
                                 TERM uu____16889  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____16905 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____16905
                                then
                                  let uu____16906 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____16906 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____16930,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____16956 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____16956
                                        then
                                          let uu____16957 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____16957
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____16964 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____16966 = lhs  in
              match uu____16966 with
              | (t1,u1,k1,args1) ->
                  let uu____16971 = rhs  in
                  (match uu____16971 with
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
                        | uu____17011 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____17021 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____17021 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____17039) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____17046 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____17046
                                     then
                                       let uu____17047 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____17047
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____17054 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17057 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17057
          then
            let uu____17058 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17058
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____17062 = FStar_Util.physical_equality t1 t2  in
             if uu____17062
             then
               let uu____17063 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____17063
             else
               ((let uu____17066 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____17066
                 then
                   let uu____17067 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____17068 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____17069 = FStar_Syntax_Print.tag_of_term t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17067
                     uu____17068 uu____17069
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let not_quote t =
                   let uu____17076 =
                     let uu____17077 = FStar_Syntax_Subst.compress t  in
                     uu____17077.FStar_Syntax_Syntax.n  in
                   match uu____17076 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____17080,FStar_Syntax_Syntax.Meta_quoted
                        uu____17081)
                       -> false
                   | uu____17092 -> true  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____17093,uu____17094)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____17119,FStar_Syntax_Syntax.Tm_delayed uu____17120)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____17145,uu____17146)
                     ->
                     let uu____17173 =
                       let uu___148_17174 = problem  in
                       let uu____17175 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_17174.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17175;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_17174.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___148_17174.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___148_17174.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_17174.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_17174.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_17174.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_17174.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_17174.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17173 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____17176,uu____17177) when
                     not_quote t1 ->
                     let uu____17184 =
                       let uu___149_17185 = problem  in
                       let uu____17186 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___149_17185.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17186;
                         FStar_TypeChecker_Common.relation =
                           (uu___149_17185.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___149_17185.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___149_17185.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___149_17185.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___149_17185.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___149_17185.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___149_17185.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___149_17185.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17184 wl
                 | (uu____17187,FStar_Syntax_Syntax.Tm_ascribed uu____17188)
                     ->
                     let uu____17215 =
                       let uu___150_17216 = problem  in
                       let uu____17217 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_17216.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___150_17216.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___150_17216.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17217;
                         FStar_TypeChecker_Common.element =
                           (uu___150_17216.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_17216.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_17216.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_17216.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_17216.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_17216.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17215 wl
                 | (uu____17218,FStar_Syntax_Syntax.Tm_meta uu____17219) when
                     not_quote t2 ->
                     let uu____17226 =
                       let uu___151_17227 = problem  in
                       let uu____17228 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_17227.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___151_17227.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___151_17227.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17228;
                         FStar_TypeChecker_Common.element =
                           (uu___151_17227.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_17227.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_17227.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_17227.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_17227.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_17227.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17226 wl
                 | (FStar_Syntax_Syntax.Tm_meta
                    (uu____17229,FStar_Syntax_Syntax.Meta_quoted
                     (t11,uu____17231)),FStar_Syntax_Syntax.Tm_meta
                    (uu____17232,FStar_Syntax_Syntax.Meta_quoted
                     (t21,uu____17234))) ->
                     let uu____17251 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____17251
                 | (FStar_Syntax_Syntax.Tm_bvar uu____17252,uu____17253) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____17254,FStar_Syntax_Syntax.Tm_bvar uu____17255) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___112_17310 =
                       match uu___112_17310 with
                       | [] -> c
                       | bs ->
                           let uu____17332 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____17332
                        in
                     let uu____17341 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____17341 with
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
                                     let uu____17483 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____17483
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____17485 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_66  ->
                                        FStar_TypeChecker_Common.CProb _0_66)
                                     uu____17485))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___113_17561 =
                       match uu___113_17561 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____17595 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____17595 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____17731 =
                                     let uu____17736 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____17737 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____17736
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____17737
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_67  ->
                                        FStar_TypeChecker_Common.TProb _0_67)
                                     uu____17731))
                 | (FStar_Syntax_Syntax.Tm_abs uu____17742,uu____17743) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17768 -> true
                       | uu____17785 -> false  in
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
                         (let uu____17832 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_17840 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_17840.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_17840.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_17840.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_17840.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_17840.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_17840.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_17840.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_17840.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_17840.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_17840.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_17840.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_17840.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_17840.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_17840.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_17840.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_17840.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_17840.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_17840.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_17840.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_17840.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_17840.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_17840.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_17840.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_17840.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_17840.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_17840.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___152_17840.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_17840.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_17840.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_17840.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_17840.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_17840.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_17840.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17832 with
                          | (uu____17843,ty,uu____17845) ->
                              let uu____17846 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17846)
                        in
                     let uu____17847 =
                       let uu____17864 = maybe_eta t1  in
                       let uu____17871 = maybe_eta t2  in
                       (uu____17864, uu____17871)  in
                     (match uu____17847 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_17913 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_17913.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_17913.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_17913.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_17913.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_17913.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_17913.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_17913.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_17913.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____17936 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17936
                          then
                            let uu____17937 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17937 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_17952 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_17952.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_17952.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_17952.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_17952.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_17952.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_17952.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_17952.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_17952.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____17976 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17976
                          then
                            let uu____17977 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17977 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_17992 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_17992.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_17992.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_17992.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_17992.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_17992.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_17992.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_17992.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_17992.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____17996 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____18013,FStar_Syntax_Syntax.Tm_abs uu____18014) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18039 -> true
                       | uu____18056 -> false  in
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
                         (let uu____18103 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_18111 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_18111.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_18111.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_18111.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_18111.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_18111.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_18111.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_18111.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_18111.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_18111.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_18111.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_18111.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_18111.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_18111.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_18111.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_18111.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_18111.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_18111.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_18111.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_18111.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_18111.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_18111.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_18111.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_18111.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_18111.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_18111.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_18111.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___152_18111.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_18111.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_18111.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_18111.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_18111.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_18111.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_18111.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18103 with
                          | (uu____18114,ty,uu____18116) ->
                              let uu____18117 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18117)
                        in
                     let uu____18118 =
                       let uu____18135 = maybe_eta t1  in
                       let uu____18142 = maybe_eta t2  in
                       (uu____18135, uu____18142)  in
                     (match uu____18118 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_18184 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_18184.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_18184.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_18184.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_18184.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_18184.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_18184.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_18184.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_18184.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18207 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18207
                          then
                            let uu____18208 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18208 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18223 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18223.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18223.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18223.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18223.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18223.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18223.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18223.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18223.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18247 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18247
                          then
                            let uu____18248 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18248 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18263 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18263.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18263.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18263.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18263.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18263.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18263.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18263.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18263.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18267 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____18299 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____18299) &&
                          (let uu____18311 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____18311))
                         &&
                         (let uu____18326 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____18326 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___114_18336 =
                                match uu___114_18336 with
                                | FStar_Syntax_Syntax.Delta_constant  -> true
                                | FStar_Syntax_Syntax.Delta_defined_at_level
                                    uu____18337 -> true
                                | uu____18338 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____18339 -> false)
                        in
                     let uu____18340 = as_refinement should_delta env wl t1
                        in
                     (match uu____18340 with
                      | (x11,phi1) ->
                          let uu____18347 =
                            as_refinement should_delta env wl t2  in
                          (match uu____18347 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____18355 =
                                   let uu____18360 = p_scope orig  in
                                   mk_problem uu____18360 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____18355
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
                                 let uu____18394 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____18394
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____18398 =
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
                                   let uu____18404 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____18404 impl
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
                                   let uu____18413 =
                                     let uu____18418 =
                                       let uu____18419 = p_scope orig  in
                                       let uu____18426 =
                                         let uu____18433 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____18433]  in
                                       FStar_List.append uu____18419
                                         uu____18426
                                        in
                                     mk_problem uu____18418 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_69  ->
                                        FStar_TypeChecker_Common.TProb _0_69)
                                     uu____18413
                                    in
                                 let uu____18442 =
                                   solve env1
                                     (let uu___155_18444 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___155_18444.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___155_18444.smt_ok);
                                        tcenv = (uu___155_18444.tcenv)
                                      })
                                    in
                                 (match uu____18442 with
                                  | Failed uu____18451 -> fallback ()
                                  | Success uu____18456 ->
                                      let guard =
                                        let uu____18460 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____18465 =
                                          let uu____18466 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____18466
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____18460
                                          uu____18465
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___156_18475 = wl1  in
                                        {
                                          attempting =
                                            (uu___156_18475.attempting);
                                          wl_deferred =
                                            (uu___156_18475.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___156_18475.defer_ok);
                                          smt_ok = (uu___156_18475.smt_ok);
                                          tcenv = (uu___156_18475.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18477,FStar_Syntax_Syntax.Tm_uvar uu____18478) ->
                     let uu____18511 = destruct_flex_t t1  in
                     let uu____18512 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18511 uu____18512
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18513;
                       FStar_Syntax_Syntax.pos = uu____18514;
                       FStar_Syntax_Syntax.vars = uu____18515;_},uu____18516),FStar_Syntax_Syntax.Tm_uvar
                    uu____18517) ->
                     let uu____18570 = destruct_flex_t t1  in
                     let uu____18571 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18570 uu____18571
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18572,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18573;
                       FStar_Syntax_Syntax.pos = uu____18574;
                       FStar_Syntax_Syntax.vars = uu____18575;_},uu____18576))
                     ->
                     let uu____18629 = destruct_flex_t t1  in
                     let uu____18630 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18629 uu____18630
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18631;
                       FStar_Syntax_Syntax.pos = uu____18632;
                       FStar_Syntax_Syntax.vars = uu____18633;_},uu____18634),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18635;
                       FStar_Syntax_Syntax.pos = uu____18636;
                       FStar_Syntax_Syntax.vars = uu____18637;_},uu____18638))
                     ->
                     let uu____18711 = destruct_flex_t t1  in
                     let uu____18712 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18711 uu____18712
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18713,uu____18714) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18731 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18731 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18738;
                       FStar_Syntax_Syntax.pos = uu____18739;
                       FStar_Syntax_Syntax.vars = uu____18740;_},uu____18741),uu____18742)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18779 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18779 t2 wl
                 | (uu____18786,FStar_Syntax_Syntax.Tm_uvar uu____18787) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____18804,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18805;
                       FStar_Syntax_Syntax.pos = uu____18806;
                       FStar_Syntax_Syntax.vars = uu____18807;_},uu____18808))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18845,FStar_Syntax_Syntax.Tm_type uu____18846) ->
                     solve_t' env
                       (let uu___157_18864 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18864.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18864.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18864.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18864.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18864.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18864.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18864.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18864.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18864.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18865;
                       FStar_Syntax_Syntax.pos = uu____18866;
                       FStar_Syntax_Syntax.vars = uu____18867;_},uu____18868),FStar_Syntax_Syntax.Tm_type
                    uu____18869) ->
                     solve_t' env
                       (let uu___157_18907 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18907.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18907.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18907.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18907.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18907.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18907.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18907.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18907.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18907.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18908,FStar_Syntax_Syntax.Tm_arrow uu____18909) ->
                     solve_t' env
                       (let uu___157_18939 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18939.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18939.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18939.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18939.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18939.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18939.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18939.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18939.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18939.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18940;
                       FStar_Syntax_Syntax.pos = uu____18941;
                       FStar_Syntax_Syntax.vars = uu____18942;_},uu____18943),FStar_Syntax_Syntax.Tm_arrow
                    uu____18944) ->
                     solve_t' env
                       (let uu___157_18994 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18994.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18994.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18994.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18994.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18994.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18994.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18994.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18994.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18994.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18995,uu____18996) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19015 =
                          let uu____19016 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19016
                           in
                        if uu____19015
                        then
                          let uu____19017 =
                            FStar_All.pipe_left
                              (fun _0_70  ->
                                 FStar_TypeChecker_Common.TProb _0_70)
                              (let uu___158_19023 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_19023.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_19023.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_19023.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_19023.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_19023.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_19023.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_19023.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_19023.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_19023.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19024 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19017 uu____19024 t2
                            wl
                        else
                          (let uu____19032 = base_and_refinement env t2  in
                           match uu____19032 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19061 =
                                      FStar_All.pipe_left
                                        (fun _0_71  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_71)
                                        (let uu___159_19067 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_19067.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_19067.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_19067.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_19067.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_19067.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_19067.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_19067.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_19067.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_19067.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19068 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19061
                                      uu____19068 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_19082 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_19082.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_19082.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19085 =
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
                                             _0_72) uu____19085
                                       in
                                    let guard =
                                      let uu____19097 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19097
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
                         uu____19105;
                       FStar_Syntax_Syntax.pos = uu____19106;
                       FStar_Syntax_Syntax.vars = uu____19107;_},uu____19108),uu____19109)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19148 =
                          let uu____19149 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19149
                           in
                        if uu____19148
                        then
                          let uu____19150 =
                            FStar_All.pipe_left
                              (fun _0_73  ->
                                 FStar_TypeChecker_Common.TProb _0_73)
                              (let uu___158_19156 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_19156.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_19156.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_19156.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_19156.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_19156.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_19156.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_19156.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_19156.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_19156.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19157 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19150 uu____19157 t2
                            wl
                        else
                          (let uu____19165 = base_and_refinement env t2  in
                           match uu____19165 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19194 =
                                      FStar_All.pipe_left
                                        (fun _0_74  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_74)
                                        (let uu___159_19200 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_19200.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_19200.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_19200.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_19200.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_19200.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_19200.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_19200.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_19200.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_19200.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19201 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19194
                                      uu____19201 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_19215 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_19215.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_19215.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19218 =
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
                                             _0_75) uu____19218
                                       in
                                    let guard =
                                      let uu____19230 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19230
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____19238,FStar_Syntax_Syntax.Tm_uvar uu____19239) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19257 = base_and_refinement env t1  in
                        match uu____19257 with
                        | (t_base,uu____19269) ->
                            solve_t env
                              (let uu___161_19283 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19283.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19283.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19283.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19283.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19283.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19283.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19283.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19283.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____19284,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19285;
                       FStar_Syntax_Syntax.pos = uu____19286;
                       FStar_Syntax_Syntax.vars = uu____19287;_},uu____19288))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19326 = base_and_refinement env t1  in
                        match uu____19326 with
                        | (t_base,uu____19338) ->
                            solve_t env
                              (let uu___161_19352 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19352.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19352.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19352.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19352.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19352.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19352.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19352.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19352.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____19353,uu____19354) ->
                     let t21 =
                       let uu____19364 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____19364  in
                     solve_t env
                       (let uu___162_19388 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___162_19388.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___162_19388.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___162_19388.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___162_19388.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___162_19388.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___162_19388.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___162_19388.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___162_19388.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___162_19388.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19389,FStar_Syntax_Syntax.Tm_refine uu____19390) ->
                     let t11 =
                       let uu____19400 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____19400  in
                     solve_t env
                       (let uu___163_19424 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___163_19424.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___163_19424.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___163_19424.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___163_19424.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___163_19424.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___163_19424.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___163_19424.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___163_19424.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___163_19424.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match uu____19427,uu____19428) ->
                     let head1 =
                       let uu____19454 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19454
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19498 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19498
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19540 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19540
                       then
                         let uu____19541 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19542 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19543 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19541 uu____19542 uu____19543
                       else ());
                      (let uu____19545 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19545
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19560 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19560
                          then
                            let guard =
                              let uu____19572 =
                                let uu____19573 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19573 = FStar_Syntax_Util.Equal  in
                              if uu____19572
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19577 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_76  ->
                                      FStar_Pervasives_Native.Some _0_76)
                                   uu____19577)
                               in
                            let uu____19580 = solve_prob orig guard [] wl  in
                            solve env uu____19580
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____19583,uu____19584) ->
                     let head1 =
                       let uu____19594 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19594
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19638 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19638
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19680 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19680
                       then
                         let uu____19681 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19682 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19683 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19681 uu____19682 uu____19683
                       else ());
                      (let uu____19685 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19685
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19700 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19700
                          then
                            let guard =
                              let uu____19712 =
                                let uu____19713 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19713 = FStar_Syntax_Util.Equal  in
                              if uu____19712
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19717 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_77  ->
                                      FStar_Pervasives_Native.Some _0_77)
                                   uu____19717)
                               in
                            let uu____19720 = solve_prob orig guard [] wl  in
                            solve env uu____19720
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____19723,uu____19724) ->
                     let head1 =
                       let uu____19728 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19728
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19772 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19772
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19814 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19814
                       then
                         let uu____19815 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19816 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19817 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19815 uu____19816 uu____19817
                       else ());
                      (let uu____19819 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19819
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19834 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19834
                          then
                            let guard =
                              let uu____19846 =
                                let uu____19847 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19847 = FStar_Syntax_Util.Equal  in
                              if uu____19846
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19851 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_78  ->
                                      FStar_Pervasives_Native.Some _0_78)
                                   uu____19851)
                               in
                            let uu____19854 = solve_prob orig guard [] wl  in
                            solve env uu____19854
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____19857,uu____19858)
                     ->
                     let head1 =
                       let uu____19862 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19862
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19906 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19906
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19948 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19948
                       then
                         let uu____19949 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19950 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19951 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19949 uu____19950 uu____19951
                       else ());
                      (let uu____19953 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19953
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19968 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19968
                          then
                            let guard =
                              let uu____19980 =
                                let uu____19981 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19981 = FStar_Syntax_Util.Equal  in
                              if uu____19980
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19985 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_79  ->
                                      FStar_Pervasives_Native.Some _0_79)
                                   uu____19985)
                               in
                            let uu____19988 = solve_prob orig guard [] wl  in
                            solve env uu____19988
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____19991,uu____19992) ->
                     let head1 =
                       let uu____19996 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19996
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20040 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20040
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20082 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20082
                       then
                         let uu____20083 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20084 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20085 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20083 uu____20084 uu____20085
                       else ());
                      (let uu____20087 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20087
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20102 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20102
                          then
                            let guard =
                              let uu____20114 =
                                let uu____20115 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20115 = FStar_Syntax_Util.Equal  in
                              if uu____20114
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20119 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_80  ->
                                      FStar_Pervasives_Native.Some _0_80)
                                   uu____20119)
                               in
                            let uu____20122 = solve_prob orig guard [] wl  in
                            solve env uu____20122
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____20125,uu____20126) ->
                     let head1 =
                       let uu____20144 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20144
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20188 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20188
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20230 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20230
                       then
                         let uu____20231 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20232 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20233 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20231 uu____20232 uu____20233
                       else ());
                      (let uu____20235 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20235
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20250 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20250
                          then
                            let guard =
                              let uu____20262 =
                                let uu____20263 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20263 = FStar_Syntax_Util.Equal  in
                              if uu____20262
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20267 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_81  ->
                                      FStar_Pervasives_Native.Some _0_81)
                                   uu____20267)
                               in
                            let uu____20270 = solve_prob orig guard [] wl  in
                            solve env uu____20270
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20273,FStar_Syntax_Syntax.Tm_match uu____20274) ->
                     let head1 =
                       let uu____20300 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20300
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20344 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20344
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20386 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20386
                       then
                         let uu____20387 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20388 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20389 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20387 uu____20388 uu____20389
                       else ());
                      (let uu____20391 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20391
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20406 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20406
                          then
                            let guard =
                              let uu____20418 =
                                let uu____20419 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20419 = FStar_Syntax_Util.Equal  in
                              if uu____20418
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20423 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_82  ->
                                      FStar_Pervasives_Native.Some _0_82)
                                   uu____20423)
                               in
                            let uu____20426 = solve_prob orig guard [] wl  in
                            solve env uu____20426
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20429,FStar_Syntax_Syntax.Tm_uinst uu____20430) ->
                     let head1 =
                       let uu____20440 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20440
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20484 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20484
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20526 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20526
                       then
                         let uu____20527 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20528 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20529 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20527 uu____20528 uu____20529
                       else ());
                      (let uu____20531 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20531
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20546 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20546
                          then
                            let guard =
                              let uu____20558 =
                                let uu____20559 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20559 = FStar_Syntax_Util.Equal  in
                              if uu____20558
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20563 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_83  ->
                                      FStar_Pervasives_Native.Some _0_83)
                                   uu____20563)
                               in
                            let uu____20566 = solve_prob orig guard [] wl  in
                            solve env uu____20566
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20569,FStar_Syntax_Syntax.Tm_name uu____20570) ->
                     let head1 =
                       let uu____20574 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20574
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20618 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20618
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20660 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20660
                       then
                         let uu____20661 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20662 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20663 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20661 uu____20662 uu____20663
                       else ());
                      (let uu____20665 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20665
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20680 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20680
                          then
                            let guard =
                              let uu____20692 =
                                let uu____20693 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20693 = FStar_Syntax_Util.Equal  in
                              if uu____20692
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20697 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_84  ->
                                      FStar_Pervasives_Native.Some _0_84)
                                   uu____20697)
                               in
                            let uu____20700 = solve_prob orig guard [] wl  in
                            solve env uu____20700
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20703,FStar_Syntax_Syntax.Tm_constant uu____20704)
                     ->
                     let head1 =
                       let uu____20708 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20708
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20752 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20752
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20794 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20794
                       then
                         let uu____20795 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20796 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20797 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20795 uu____20796 uu____20797
                       else ());
                      (let uu____20799 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20799
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20814 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20814
                          then
                            let guard =
                              let uu____20826 =
                                let uu____20827 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20827 = FStar_Syntax_Util.Equal  in
                              if uu____20826
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20831 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_85  ->
                                      FStar_Pervasives_Native.Some _0_85)
                                   uu____20831)
                               in
                            let uu____20834 = solve_prob orig guard [] wl  in
                            solve env uu____20834
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20837,FStar_Syntax_Syntax.Tm_fvar uu____20838) ->
                     let head1 =
                       let uu____20842 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20842
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20886 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20886
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20928 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20928
                       then
                         let uu____20929 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20930 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20931 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20929 uu____20930 uu____20931
                       else ());
                      (let uu____20933 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20933
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20948 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20948
                          then
                            let guard =
                              let uu____20960 =
                                let uu____20961 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20961 = FStar_Syntax_Util.Equal  in
                              if uu____20960
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20965 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_86  ->
                                      FStar_Pervasives_Native.Some _0_86)
                                   uu____20965)
                               in
                            let uu____20968 = solve_prob orig guard [] wl  in
                            solve env uu____20968
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20971,FStar_Syntax_Syntax.Tm_app uu____20972) ->
                     let head1 =
                       let uu____20990 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20990
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21034 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21034
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21076 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21076
                       then
                         let uu____21077 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21078 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21079 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21077 uu____21078 uu____21079
                       else ());
                      (let uu____21081 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21081
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21096 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21096
                          then
                            let guard =
                              let uu____21108 =
                                let uu____21109 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21109 = FStar_Syntax_Util.Equal  in
                              if uu____21108
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21113 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_87  ->
                                      FStar_Pervasives_Native.Some _0_87)
                                   uu____21113)
                               in
                            let uu____21116 = solve_prob orig guard [] wl  in
                            solve env uu____21116
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____21119,FStar_Syntax_Syntax.Tm_let uu____21120) ->
                     let uu____21145 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____21145
                     then
                       let uu____21146 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____21146
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____21148,uu____21149) ->
                     let uu____21162 =
                       let uu____21167 =
                         let uu____21168 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21169 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21170 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21171 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21168 uu____21169 uu____21170 uu____21171
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21167)
                        in
                     FStar_Errors.raise_error uu____21162
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____21172,FStar_Syntax_Syntax.Tm_let uu____21173) ->
                     let uu____21186 =
                       let uu____21191 =
                         let uu____21192 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21193 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21194 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21195 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21192 uu____21193 uu____21194 uu____21195
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21191)
                        in
                     FStar_Errors.raise_error uu____21186
                       t1.FStar_Syntax_Syntax.pos
                 | uu____21196 -> giveup env "head tag mismatch" orig)))))

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
          let uu____21224 = p_scope orig  in
          mk_problem uu____21224 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____21233 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21233
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____21235 =
               let uu____21236 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21237 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21236 uu____21237
                in
             giveup env uu____21235 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____21257  ->
                    fun uu____21258  ->
                      match (uu____21257, uu____21258) with
                      | ((a1,uu____21276),(a2,uu____21278)) ->
                          let uu____21287 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21287)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____21297 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____21297  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21321 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21328)::[] -> wp1
              | uu____21345 ->
                  let uu____21354 =
                    let uu____21355 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21355
                     in
                  failwith uu____21354
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21363 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21363]
              | x -> x  in
            let uu____21365 =
              let uu____21374 =
                let uu____21375 =
                  let uu____21376 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21376 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21375  in
              [uu____21374]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21365;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21377 = lift_c1 ()  in solve_eq uu____21377 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___115_21383  ->
                       match uu___115_21383 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21384 -> false))
                in
             let uu____21385 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21419)::uu____21420,(wp2,uu____21422)::uu____21423)
                   -> (wp1, wp2)
               | uu____21480 ->
                   let uu____21501 =
                     let uu____21506 =
                       let uu____21507 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21508 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21507 uu____21508
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21506)
                      in
                   FStar_Errors.raise_error uu____21501
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21385 with
             | (wpc1,wpc2) ->
                 let uu____21527 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21527
                 then
                   let uu____21530 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21530 wl
                 else
                   (let uu____21534 =
                      let uu____21541 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21541  in
                    match uu____21534 with
                    | (c2_decl,qualifiers) ->
                        let uu____21562 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21562
                        then
                          let c1_repr =
                            let uu____21566 =
                              let uu____21567 =
                                let uu____21568 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21568  in
                              let uu____21569 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21567 uu____21569
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21566
                             in
                          let c2_repr =
                            let uu____21571 =
                              let uu____21572 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21573 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21572 uu____21573
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21571
                             in
                          let prob =
                            let uu____21575 =
                              let uu____21580 =
                                let uu____21581 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21582 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21581
                                  uu____21582
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21580
                               in
                            FStar_TypeChecker_Common.TProb uu____21575  in
                          let wl1 =
                            let uu____21584 =
                              let uu____21587 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21587  in
                            solve_prob orig uu____21584 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21596 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21596
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21599 =
                                     let uu____21602 =
                                       let uu____21603 =
                                         let uu____21618 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21619 =
                                           let uu____21622 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21623 =
                                             let uu____21626 =
                                               let uu____21627 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21627
                                                in
                                             [uu____21626]  in
                                           uu____21622 :: uu____21623  in
                                         (uu____21618, uu____21619)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21603
                                        in
                                     FStar_Syntax_Syntax.mk uu____21602  in
                                   uu____21599 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21636 =
                                    let uu____21639 =
                                      let uu____21640 =
                                        let uu____21655 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21656 =
                                          let uu____21659 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21660 =
                                            let uu____21663 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21664 =
                                              let uu____21667 =
                                                let uu____21668 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21668
                                                 in
                                              [uu____21667]  in
                                            uu____21663 :: uu____21664  in
                                          uu____21659 :: uu____21660  in
                                        (uu____21655, uu____21656)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21640
                                       in
                                    FStar_Syntax_Syntax.mk uu____21639  in
                                  uu____21636 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21675 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21675
                              in
                           let wl1 =
                             let uu____21685 =
                               let uu____21688 =
                                 let uu____21691 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21691 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21688
                                in
                             solve_prob orig uu____21685 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21704 = FStar_Util.physical_equality c1 c2  in
        if uu____21704
        then
          let uu____21705 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21705
        else
          ((let uu____21708 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21708
            then
              let uu____21709 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21710 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21709
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21710
            else ());
           (let uu____21712 =
              let uu____21717 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21718 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21717, uu____21718)  in
            match uu____21712 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21722),FStar_Syntax_Syntax.Total
                    (t2,uu____21724)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21741 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21741 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21744,FStar_Syntax_Syntax.Total uu____21745) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21763),FStar_Syntax_Syntax.Total
                    (t2,uu____21765)) ->
                     let uu____21782 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21782 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21786),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21788)) ->
                     let uu____21805 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21805 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21809),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21811)) ->
                     let uu____21828 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21828 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21831,FStar_Syntax_Syntax.Comp uu____21832) ->
                     let uu____21841 =
                       let uu___164_21846 = problem  in
                       let uu____21851 =
                         let uu____21852 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21852
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21846.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21851;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21846.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21846.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21846.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21846.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21846.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21846.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21846.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21846.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21841 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21853,FStar_Syntax_Syntax.Comp uu____21854) ->
                     let uu____21863 =
                       let uu___164_21868 = problem  in
                       let uu____21873 =
                         let uu____21874 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21874
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21868.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21873;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21868.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21868.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21868.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21868.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21868.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21868.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21868.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21868.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21863 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21875,FStar_Syntax_Syntax.GTotal uu____21876) ->
                     let uu____21885 =
                       let uu___165_21890 = problem  in
                       let uu____21895 =
                         let uu____21896 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21896
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21890.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21890.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21890.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21895;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21890.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21890.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21890.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21890.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21890.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21890.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21885 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21897,FStar_Syntax_Syntax.Total uu____21898) ->
                     let uu____21907 =
                       let uu___165_21912 = problem  in
                       let uu____21917 =
                         let uu____21918 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21918
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21912.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21912.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21912.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21917;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21912.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21912.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21912.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21912.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21912.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21912.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21907 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21919,FStar_Syntax_Syntax.Comp uu____21920) ->
                     let uu____21921 =
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
                     if uu____21921
                     then
                       let uu____21922 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21922 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21928 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21938 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21939 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21938, uu____21939))
                             in
                          match uu____21928 with
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
                           (let uu____21946 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21946
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21948 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21948 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21951 =
                                  let uu____21952 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21953 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21952 uu____21953
                                   in
                                giveup env uu____21951 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21958 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21996  ->
              match uu____21996 with
              | (uu____22009,uu____22010,u,uu____22012,uu____22013,uu____22014)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21958 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____22045 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____22045 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____22063 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____22091  ->
                match uu____22091 with
                | (u1,u2) ->
                    let uu____22098 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____22099 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____22098 uu____22099))
         in
      FStar_All.pipe_right uu____22063 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____22116,[])) -> "{}"
      | uu____22141 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____22158 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____22158
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____22161 =
              FStar_List.map
                (fun uu____22171  ->
                   match uu____22171 with
                   | (uu____22176,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____22161 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____22181 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____22181 imps
  
let new_t_problem :
  'Auu____22189 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____22189 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____22189)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____22223 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____22223
                then
                  let uu____22224 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____22225 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22224
                    (rel_to_string rel) uu____22225
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
            let uu____22249 =
              let uu____22252 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____22252
               in
            FStar_Syntax_Syntax.new_bv uu____22249 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____22261 =
              let uu____22264 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____22264
               in
            let uu____22267 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____22261 uu____22267  in
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
          let uu____22297 = FStar_Options.eager_inference ()  in
          if uu____22297
          then
            let uu___166_22298 = probs  in
            {
              attempting = (uu___166_22298.attempting);
              wl_deferred = (uu___166_22298.wl_deferred);
              ctr = (uu___166_22298.ctr);
              defer_ok = false;
              smt_ok = (uu___166_22298.smt_ok);
              tcenv = (uu___166_22298.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22309 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22309
              then
                let uu____22310 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22310
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
          ((let uu____22324 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22324
            then
              let uu____22325 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22325
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22329 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22329
             then
               let uu____22330 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22330
             else ());
            (let f2 =
               let uu____22333 =
                 let uu____22334 = FStar_Syntax_Util.unmeta f1  in
                 uu____22334.FStar_Syntax_Syntax.n  in
               match uu____22333 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22338 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___167_22339 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_22339.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_22339.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_22339.FStar_TypeChecker_Env.implicits)
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
            let uu____22358 =
              let uu____22359 =
                let uu____22360 =
                  let uu____22361 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22361
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22360;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22359  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____22358
  
let with_guard_no_simp :
  'Auu____22388 .
    'Auu____22388 ->
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
            let uu____22408 =
              let uu____22409 =
                let uu____22410 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22410
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22409;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22408
  
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
          (let uu____22448 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22448
           then
             let uu____22449 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22450 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22449
               uu____22450
           else ());
          (let prob =
             let uu____22453 =
               let uu____22458 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22458
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22453
              in
           let g =
             let uu____22466 =
               let uu____22469 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22469
                 (fun uu____22471  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22466  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22489 = try_teq true env t1 t2  in
        match uu____22489 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22493 = FStar_TypeChecker_Env.get_range env  in
              let uu____22494 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22493 uu____22494);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22501 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22501
              then
                let uu____22502 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22503 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22504 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22502
                  uu____22503 uu____22504
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
          let uu____22518 = FStar_TypeChecker_Env.get_range env  in
          let uu____22519 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22518 uu____22519
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22536 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22536
         then
           let uu____22537 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22538 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22537
             uu____22538
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22543 =
             let uu____22548 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22548 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22543
            in
         let uu____22553 =
           let uu____22556 = singleton env prob  in
           solve_and_commit env uu____22556
             (fun uu____22558  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22553)
  
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
      fun uu____22587  ->
        match uu____22587 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22626 =
                 let uu____22631 =
                   let uu____22632 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22633 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22632 uu____22633
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22631)  in
               let uu____22634 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22626 uu____22634)
               in
            let equiv1 v1 v' =
              let uu____22642 =
                let uu____22647 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22648 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22647, uu____22648)  in
              match uu____22642 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22667 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22697 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22697 with
                      | FStar_Syntax_Syntax.U_unif uu____22704 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22733  ->
                                    match uu____22733 with
                                    | (u,v') ->
                                        let uu____22742 = equiv1 v1 v'  in
                                        if uu____22742
                                        then
                                          let uu____22745 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22745 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22761 -> []))
               in
            let uu____22766 =
              let wl =
                let uu___168_22770 = empty_worklist env  in
                {
                  attempting = (uu___168_22770.attempting);
                  wl_deferred = (uu___168_22770.wl_deferred);
                  ctr = (uu___168_22770.ctr);
                  defer_ok = false;
                  smt_ok = (uu___168_22770.smt_ok);
                  tcenv = (uu___168_22770.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22788  ->
                      match uu____22788 with
                      | (lb,v1) ->
                          let uu____22795 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22795 with
                           | USolved wl1 -> ()
                           | uu____22797 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22805 =
              match uu____22805 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22814) -> true
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
                      uu____22837,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22839,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22850) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22857,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22865 -> false)
               in
            let uu____22870 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22885  ->
                      match uu____22885 with
                      | (u,v1) ->
                          let uu____22892 = check_ineq (u, v1)  in
                          if uu____22892
                          then true
                          else
                            ((let uu____22895 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22895
                              then
                                let uu____22896 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22897 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22896
                                  uu____22897
                              else ());
                             false)))
               in
            if uu____22870
            then ()
            else
              ((let uu____22901 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22901
                then
                  ((let uu____22903 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22903);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22913 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22913))
                else ());
               (let uu____22923 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22923))
  
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
      let fail1 uu____22971 =
        match uu____22971 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22985 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22985
       then
         let uu____22986 = wl_to_string wl  in
         let uu____22987 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22986 uu____22987
       else ());
      (let g1 =
         let uu____23002 = solve_and_commit env wl fail1  in
         match uu____23002 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___169_23015 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___169_23015.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_23015.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_23015.FStar_TypeChecker_Env.implicits)
             }
         | uu____23020 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___170_23024 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___170_23024.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___170_23024.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___170_23024.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____23050 = FStar_ST.op_Bang last_proof_ns  in
    match uu____23050 with
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
            let uu___171_23153 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___171_23153.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___171_23153.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___171_23153.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____23154 =
            let uu____23155 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____23155  in
          if uu____23154
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____23163 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____23164 =
                       let uu____23165 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____23165
                        in
                     FStar_Errors.diag uu____23163 uu____23164)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____23169 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____23170 =
                        let uu____23171 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____23171
                         in
                      FStar_Errors.diag uu____23169 uu____23170)
                   else ();
                   (let uu____23174 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____23174 "discharge_guard'"
                      env vc1);
                   (let uu____23175 = check_trivial vc1  in
                    match uu____23175 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____23182 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23183 =
                                let uu____23184 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____23184
                                 in
                              FStar_Errors.diag uu____23182 uu____23183)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____23189 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23190 =
                                let uu____23191 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____23191
                                 in
                              FStar_Errors.diag uu____23189 uu____23190)
                           else ();
                           (let vcs =
                              let uu____23202 = FStar_Options.use_tactics ()
                                 in
                              if uu____23202
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23221  ->
                                     (let uu____23223 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23223);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____23225 =
                                   let uu____23232 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23232)  in
                                 [uu____23225])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23266  ->
                                    match uu____23266 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____23277 = check_trivial goal1
                                           in
                                        (match uu____23277 with
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
                                                (let uu____23285 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23286 =
                                                   let uu____23287 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____23288 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23287 uu____23288
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23285 uu____23286)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23291 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23292 =
                                                   let uu____23293 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23293
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23291 uu____23292)
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
      let uu____23303 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23303 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23309 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23309
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23316 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23316 with
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
          let uu____23335 = FStar_Syntax_Unionfind.find u  in
          match uu____23335 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23338 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23356 = acc  in
          match uu____23356 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23442 = hd1  in
                   (match uu____23442 with
                    | (uu____23455,env,u,tm,k,r) ->
                        let uu____23461 = unresolved u  in
                        if uu____23461
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___172_23491 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___172_23491.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___172_23491.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___172_23491.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___172_23491.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___172_23491.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___172_23491.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___172_23491.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___172_23491.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___172_23491.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___172_23491.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___172_23491.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___172_23491.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___172_23491.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___172_23491.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___172_23491.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___172_23491.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___172_23491.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___172_23491.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___172_23491.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___172_23491.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___172_23491.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___172_23491.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___172_23491.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___172_23491.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___172_23491.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___172_23491.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___172_23491.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___172_23491.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___172_23491.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___172_23491.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___172_23491.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___172_23491.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___172_23491.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___172_23491.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___172_23491.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23494 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23494
                            then
                              let uu____23495 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23496 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23497 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23495 uu____23496 uu____23497
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23508 =
                                      let uu____23517 =
                                        let uu____23524 =
                                          let uu____23525 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23526 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23525 uu____23526
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23524, r)
                                         in
                                      [uu____23517]  in
                                    FStar_Errors.add_errors uu____23508);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___175_23540 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___175_23540.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___175_23540.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___175_23540.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23543 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23549  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23543 with
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
        let uu___176_23577 = g  in
        let uu____23578 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_23577.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_23577.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___176_23577.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23578
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
        let uu____23632 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23632 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23645 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23645
      | (reason,uu____23647,uu____23648,e,t,r)::uu____23652 ->
          let uu____23679 =
            let uu____23684 =
              let uu____23685 = FStar_Syntax_Print.term_to_string t  in
              let uu____23686 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23685 uu____23686
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23684)
             in
          FStar_Errors.raise_error uu____23679 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___177_23693 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___177_23693.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___177_23693.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___177_23693.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23716 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23716 with
      | FStar_Pervasives_Native.Some uu____23721 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23731 = try_teq false env t1 t2  in
        match uu____23731 with
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
        (let uu____23751 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23751
         then
           let uu____23752 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23753 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23752
             uu____23753
         else ());
        (let uu____23755 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23755 with
         | (prob,x) ->
             let g =
               let uu____23771 =
                 let uu____23774 = singleton' env prob true  in
                 solve_and_commit env uu____23774
                   (fun uu____23776  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23771  in
             ((let uu____23786 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23786
               then
                 let uu____23787 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23788 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23789 =
                   let uu____23790 = FStar_Util.must g  in
                   guard_to_string env uu____23790  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23787 uu____23788 uu____23789
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
        let uu____23818 = check_subtyping env t1 t2  in
        match uu____23818 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23837 =
              let uu____23838 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23838 g  in
            FStar_Pervasives_Native.Some uu____23837
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23850 = check_subtyping env t1 t2  in
        match uu____23850 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23869 =
              let uu____23870 =
                let uu____23871 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23871]  in
              close_guard env uu____23870 g  in
            FStar_Pervasives_Native.Some uu____23869
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23882 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23882
         then
           let uu____23883 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23884 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23883
             uu____23884
         else ());
        (let uu____23886 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23886 with
         | (prob,x) ->
             let g =
               let uu____23896 =
                 let uu____23899 = singleton' env prob false  in
                 solve_and_commit env uu____23899
                   (fun uu____23901  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23896  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23912 =
                      let uu____23913 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23913]  in
                    close_guard env uu____23912 g1  in
                  discharge_guard_nosmt env g2))
  